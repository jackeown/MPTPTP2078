%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0977+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 4.07s
% Output     : Refutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  637 (1316 expanded)
%              Number of leaves         :  193 ( 563 expanded)
%              Depth                    :   10
%              Number of atoms          : 2769 (5423 expanded)
%              Number of equality atoms :  271 ( 554 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4660,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3672,f3676,f3717,f3721,f3728,f3732,f3739,f3743,f3748,f3750,f3752,f3756,f3760,f3764,f3765,f3769,f3771,f3779,f3786,f3787,f3791,f3795,f3802,f3803,f3806,f3815,f3824,f3827,f3840,f3844,f3846,f3858,f3870,f3887,f3961,f3965,f3969,f3976,f3983,f3987,f3991,f3992,f3996,f4000,f4004,f4008,f4012,f4016,f4020,f4024,f4028,f4032,f4036,f4040,f4044,f4048,f4052,f4057,f4062,f4068,f4075,f4080,f4099,f4101,f4103,f4143,f4150,f4151,f4158,f4162,f4169,f4176,f4183,f4191,f4198,f4205,f4213,f4305,f4313,f4317,f4321,f4326,f4330,f4334,f4343,f4512,f4516,f4520,f4562,f4563,f4568,f4655,f4657,f4659])).

fof(f4659,plain,
    ( ~ spl172_7
    | ~ spl172_15
    | spl172_63 ),
    inference(avatar_contradiction_clause,[],[f4658])).

fof(f4658,plain,
    ( $false
    | ~ spl172_7
    | ~ spl172_15
    | spl172_63 ),
    inference(global_subsumption,[],[f3755,f3720,f4651])).

fof(f4651,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | spl172_63 ),
    inference(resolution,[],[f4079,f3236])).

fof(f3236,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2452])).

fof(f2452,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1934])).

fof(f1934,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f4079,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK2)
    | spl172_63 ),
    inference(avatar_component_clause,[],[f4078])).

fof(f4078,plain,
    ( spl172_63
  <=> r1_tarski(k1_relat_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_63])])).

fof(f3720,plain,
    ( v1_relat_1(sK4)
    | ~ spl172_7 ),
    inference(avatar_component_clause,[],[f3719])).

fof(f3719,plain,
    ( spl172_7
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_7])])).

fof(f3755,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl172_15 ),
    inference(avatar_component_clause,[],[f3754])).

fof(f3754,plain,
    ( spl172_15
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_15])])).

fof(f4657,plain,
    ( ~ spl172_7
    | ~ spl172_15
    | spl172_63 ),
    inference(avatar_contradiction_clause,[],[f4656])).

fof(f4656,plain,
    ( $false
    | ~ spl172_7
    | ~ spl172_15
    | spl172_63 ),
    inference(global_subsumption,[],[f3755,f3720,f4651])).

fof(f4655,plain,
    ( ~ spl172_7
    | ~ spl172_15
    | spl172_63 ),
    inference(avatar_contradiction_clause,[],[f4654])).

fof(f4654,plain,
    ( $false
    | ~ spl172_7
    | ~ spl172_15
    | spl172_63 ),
    inference(global_subsumption,[],[f3755,f3720,f4651])).

fof(f4568,plain,(
    spl172_89 ),
    inference(avatar_contradiction_clause,[],[f4564])).

fof(f4564,plain,
    ( $false
    | spl172_89 ),
    inference(resolution,[],[f4329,f2917])).

fof(f2917,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f4329,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl172_89 ),
    inference(avatar_component_clause,[],[f4328])).

fof(f4328,plain,
    ( spl172_89
  <=> r1_tarski(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_89])])).

fof(f4563,plain,
    ( ~ spl172_87
    | spl172_86 ),
    inference(avatar_split_clause,[],[f4554,f4315,f4319])).

fof(f4319,plain,
    ( spl172_87
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_87])])).

fof(f4315,plain,
    ( spl172_86
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_86])])).

fof(f4554,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl172_86 ),
    inference(resolution,[],[f4316,f2950])).

fof(f2950,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1734])).

fof(f1734,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f4316,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl172_86 ),
    inference(avatar_component_clause,[],[f4315])).

fof(f4562,plain,(
    spl172_87 ),
    inference(avatar_contradiction_clause,[],[f4557])).

fof(f4557,plain,
    ( $false
    | spl172_87 ),
    inference(resolution,[],[f4320,f2957])).

fof(f2957,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4320,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl172_87 ),
    inference(avatar_component_clause,[],[f4319])).

fof(f4520,plain,
    ( ~ spl172_94
    | ~ spl172_67
    | spl172_77 ),
    inference(avatar_split_clause,[],[f4300,f4189,f4153,f4518])).

fof(f4518,plain,
    ( spl172_94
  <=> r2_relset_1(sK2,sK3,sK107(k1_xboole_0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_94])])).

fof(f4153,plain,
    ( spl172_67
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_67])])).

fof(f4189,plain,
    ( spl172_77
  <=> r2_relset_1(sK2,sK3,sK107(k2_zfmisc_1(sK2,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_77])])).

fof(f4300,plain,
    ( ~ r2_relset_1(sK2,sK3,sK107(k1_xboole_0),sK4)
    | ~ spl172_67
    | spl172_77 ),
    inference(backward_demodulation,[],[f4190,f4154])).

fof(f4154,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl172_67 ),
    inference(avatar_component_clause,[],[f4153])).

fof(f4190,plain,
    ( ~ r2_relset_1(sK2,sK3,sK107(k2_zfmisc_1(sK2,sK3)),sK4)
    | spl172_77 ),
    inference(avatar_component_clause,[],[f4189])).

fof(f4516,plain,
    ( ~ spl172_93
    | ~ spl172_67
    | spl172_74 ),
    inference(avatar_split_clause,[],[f4299,f4178,f4153,f4514])).

fof(f4514,plain,
    ( spl172_93
  <=> r2_relset_1(sK2,sK3,sK105(k1_xboole_0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_93])])).

fof(f4178,plain,
    ( spl172_74
  <=> r2_relset_1(sK2,sK3,sK105(k2_zfmisc_1(sK2,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_74])])).

fof(f4299,plain,
    ( ~ r2_relset_1(sK2,sK3,sK105(k1_xboole_0),sK4)
    | ~ spl172_67
    | spl172_74 ),
    inference(backward_demodulation,[],[f4179,f4154])).

fof(f4179,plain,
    ( ~ r2_relset_1(sK2,sK3,sK105(k2_zfmisc_1(sK2,sK3)),sK4)
    | spl172_74 ),
    inference(avatar_component_clause,[],[f4178])).

fof(f4512,plain,
    ( ~ spl172_92
    | ~ spl172_67
    | spl172_70 ),
    inference(avatar_split_clause,[],[f4508,f4164,f4153,f4510])).

fof(f4510,plain,
    ( spl172_92
  <=> r2_relset_1(sK2,sK3,sK9(k1_tarski(k1_xboole_0)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_92])])).

fof(f4164,plain,
    ( spl172_70
  <=> r2_relset_1(sK2,sK3,sK9(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_70])])).

fof(f4508,plain,
    ( ~ r2_relset_1(sK2,sK3,sK9(k1_tarski(k1_xboole_0)),sK4)
    | ~ spl172_67
    | spl172_70 ),
    inference(forward_demodulation,[],[f4298,f3188])).

fof(f3188,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f4298,plain,
    ( ~ r2_relset_1(sK2,sK3,sK9(k1_zfmisc_1(k1_xboole_0)),sK4)
    | ~ spl172_67
    | spl172_70 ),
    inference(backward_demodulation,[],[f4165,f4154])).

fof(f4165,plain,
    ( ~ r2_relset_1(sK2,sK3,sK9(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))),sK4)
    | spl172_70 ),
    inference(avatar_component_clause,[],[f4164])).

fof(f4343,plain,
    ( ~ spl172_91
    | spl172_34
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4339,f4153,f3856,f4341])).

fof(f4341,plain,
    ( spl172_91
  <=> r2_hidden(k1_tarski(k1_xboole_0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_91])])).

fof(f3856,plain,
    ( spl172_34
  <=> r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_34])])).

fof(f4339,plain,
    ( ~ r2_hidden(k1_tarski(k1_xboole_0),sK4)
    | spl172_34
    | ~ spl172_67 ),
    inference(forward_demodulation,[],[f4233,f3188])).

fof(f4233,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK4)
    | spl172_34
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3857,f4154])).

fof(f3857,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)),sK4)
    | spl172_34 ),
    inference(avatar_component_clause,[],[f3856])).

fof(f4334,plain,
    ( ~ spl172_90
    | spl172_33
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4228,f4153,f3842,f4332])).

fof(f4332,plain,
    ( spl172_90
  <=> r2_hidden(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_90])])).

fof(f3842,plain,
    ( spl172_33
  <=> r2_hidden(k2_zfmisc_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_33])])).

fof(f4228,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4)
    | spl172_33
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3843,f4154])).

fof(f3843,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK4)
    | spl172_33 ),
    inference(avatar_component_clause,[],[f3842])).

fof(f4330,plain,
    ( ~ spl172_89
    | spl172_31
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4227,f4153,f3835,f4328])).

fof(f3835,plain,
    ( spl172_31
  <=> r1_tarski(k2_zfmisc_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_31])])).

fof(f4227,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl172_31
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3836,f4154])).

fof(f3836,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),sK4)
    | spl172_31 ),
    inference(avatar_component_clause,[],[f3835])).

fof(f4326,plain,
    ( spl172_88
    | ~ spl172_26
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4322,f4153,f3800,f4324])).

fof(f4324,plain,
    ( spl172_88
  <=> r2_hidden(sK4,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_88])])).

fof(f3800,plain,
    ( spl172_26
  <=> r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_26])])).

fof(f4322,plain,
    ( r2_hidden(sK4,k1_tarski(k1_xboole_0))
    | ~ spl172_26
    | ~ spl172_67 ),
    inference(forward_demodulation,[],[f4226,f3188])).

fof(f4226,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl172_26
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3801,f4154])).

fof(f3801,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl172_26 ),
    inference(avatar_component_clause,[],[f3800])).

fof(f4321,plain,
    ( ~ spl172_87
    | spl172_22
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4223,f4153,f3784,f4319])).

fof(f3784,plain,
    ( spl172_22
  <=> v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_22])])).

fof(f4223,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl172_22
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3785,f4154])).

fof(f3785,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3))
    | spl172_22 ),
    inference(avatar_component_clause,[],[f3784])).

fof(f4317,plain,
    ( ~ spl172_86
    | spl172_20
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4222,f4153,f3776,f4315])).

fof(f3776,plain,
    ( spl172_20
  <=> v1_funct_1(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_20])])).

fof(f4222,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl172_20
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3777,f4154])).

fof(f3777,plain,
    ( ~ v1_funct_1(k2_zfmisc_1(sK2,sK3))
    | spl172_20 ),
    inference(avatar_component_clause,[],[f3776])).

fof(f4313,plain,
    ( spl172_85
    | ~ spl172_18
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4221,f4153,f3767,f4311])).

fof(f4311,plain,
    ( spl172_85
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_85])])).

fof(f3767,plain,
    ( spl172_18
  <=> r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_18])])).

fof(f4221,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl172_18
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3768,f4154])).

fof(f3768,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
    | ~ spl172_18 ),
    inference(avatar_component_clause,[],[f3767])).

fof(f4305,plain,
    ( spl172_84
    | ~ spl172_3
    | ~ spl172_67 ),
    inference(avatar_split_clause,[],[f4301,f4153,f3674,f4303])).

fof(f4303,plain,
    ( spl172_84
  <=> m1_subset_1(sK4,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_84])])).

fof(f3674,plain,
    ( spl172_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_3])])).

fof(f4301,plain,
    ( m1_subset_1(sK4,k1_tarski(k1_xboole_0))
    | ~ spl172_3
    | ~ spl172_67 ),
    inference(forward_demodulation,[],[f4214,f3188])).

fof(f4214,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl172_3
    | ~ spl172_67 ),
    inference(backward_demodulation,[],[f3675,f4154])).

fof(f3675,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl172_3 ),
    inference(avatar_component_clause,[],[f3674])).

fof(f4213,plain,
    ( spl172_82
    | ~ spl172_83
    | ~ spl172_3
    | spl172_11
    | spl172_13 ),
    inference(avatar_split_clause,[],[f4206,f3741,f3734,f3674,f4211,f4208])).

fof(f4208,plain,
    ( spl172_82
  <=> sK4 = sK130(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_82])])).

fof(f4211,plain,
    ( spl172_83
  <=> r2_relset_1(sK2,sK3,sK130(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_83])])).

fof(f3734,plain,
    ( spl172_11
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_11])])).

fof(f3741,plain,
    ( spl172_13
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_13])])).

fof(f4206,plain,
    ( ~ r2_relset_1(sK2,sK3,sK130(sK2,sK3),sK4)
    | sK4 = sK130(sK2,sK3)
    | ~ spl172_3
    | spl172_11
    | spl172_13 ),
    inference(global_subsumption,[],[f3742,f3735,f4139])).

fof(f4139,plain,
    ( sK4 = sK130(sK2,sK3)
    | ~ r2_relset_1(sK2,sK3,sK130(sK2,sK3),sK4)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f3228])).

fof(f3228,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK130(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2451])).

fof(f2451,plain,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(sK130(X0,X1))
        & v1_funct_1(sK130(X0,X1))
        & v5_relat_1(sK130(X0,X1),X1)
        & v4_relat_1(sK130(X0,X1),X0)
        & v1_relat_1(sK130(X0,X1))
        & m1_subset_1(sK130(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK130])],[f1929,f2450])).

fof(f2450,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_xboole_0(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ~ v1_xboole_0(sK130(X0,X1))
        & v1_funct_1(sK130(X0,X1))
        & v5_relat_1(sK130(X0,X1),X1)
        & v4_relat_1(sK130(X0,X1),X0)
        & v1_relat_1(sK130(X0,X1))
        & m1_subset_1(sK130(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1929,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_xboole_0(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1928])).

fof(f1928,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_xboole_0(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1484])).

fof(f1484,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ? [X2] :
          ( ~ v1_xboole_0(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_partfun1)).

fof(f3677,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | sK4 = X0
        | ~ r2_relset_1(sK2,sK3,X0,sK4) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2558])).

fof(f2558,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2166])).

fof(f2166,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1517])).

fof(f1517,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1516])).

fof(f1516,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1236])).

fof(f1236,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f3735,plain,
    ( ~ v1_xboole_0(sK3)
    | spl172_11 ),
    inference(avatar_component_clause,[],[f3734])).

fof(f3742,plain,
    ( ~ v1_xboole_0(sK2)
    | spl172_13 ),
    inference(avatar_component_clause,[],[f3741])).

fof(f4205,plain,
    ( ~ spl172_80
    | spl172_81
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4138,f3674,f4203,f4200])).

fof(f4200,plain,
    ( spl172_80
  <=> r2_relset_1(sK2,sK3,sK127(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_80])])).

fof(f4203,plain,
    ( spl172_81
  <=> sK4 = sK127(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_81])])).

fof(f4138,plain,
    ( sK4 = sK127(sK2,sK3)
    | ~ r2_relset_1(sK2,sK3,sK127(sK2,sK3),sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f3214])).

fof(f3214,plain,(
    ! [X0,X1] : m1_subset_1(sK127(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f2445])).

fof(f2445,plain,(
    ! [X0,X1] :
      ( v5_relat_1(sK127(X0,X1),X1)
      & v4_relat_1(sK127(X0,X1),X0)
      & v1_relat_1(sK127(X0,X1))
      & v1_xboole_0(sK127(X0,X1))
      & m1_subset_1(sK127(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK127])],[f1482,f2444])).

fof(f2444,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & v1_xboole_0(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v5_relat_1(sK127(X0,X1),X1)
        & v4_relat_1(sK127(X0,X1),X0)
        & v1_relat_1(sK127(X0,X1))
        & v1_xboole_0(sK127(X0,X1))
        & m1_subset_1(sK127(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1482,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

fof(f4198,plain,
    ( ~ spl172_78
    | spl172_79
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4137,f3674,f4196,f4193])).

fof(f4193,plain,
    ( spl172_78
  <=> r2_relset_1(sK2,sK3,sK126(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_78])])).

fof(f4196,plain,
    ( spl172_79
  <=> sK4 = sK126(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_79])])).

fof(f4137,plain,
    ( sK4 = sK126(sK2,sK3)
    | ~ r2_relset_1(sK2,sK3,sK126(sK2,sK3),sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f3209])).

fof(f3209,plain,(
    ! [X0,X1] : m1_subset_1(sK126(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f2443])).

fof(f2443,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK126(X0,X1))
      & v5_relat_1(sK126(X0,X1),X1)
      & v4_relat_1(sK126(X0,X1),X0)
      & v1_relat_1(sK126(X0,X1))
      & m1_subset_1(sK126(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK126])],[f1481,f2442])).

fof(f2442,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_1(sK126(X0,X1))
        & v5_relat_1(sK126(X0,X1),X1)
        & v4_relat_1(sK126(X0,X1),X0)
        & v1_relat_1(sK126(X0,X1))
        & m1_subset_1(sK126(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1481,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_partfun1)).

fof(f4191,plain,
    ( spl172_76
    | ~ spl172_77
    | ~ spl172_3
    | spl172_22 ),
    inference(avatar_split_clause,[],[f4184,f3784,f3674,f4189,f4186])).

fof(f4186,plain,
    ( spl172_76
  <=> sK4 = sK107(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_76])])).

fof(f4184,plain,
    ( ~ r2_relset_1(sK2,sK3,sK107(k2_zfmisc_1(sK2,sK3)),sK4)
    | sK4 = sK107(k2_zfmisc_1(sK2,sK3))
    | ~ spl172_3
    | spl172_22 ),
    inference(global_subsumption,[],[f3785,f4136])).

fof(f4136,plain,
    ( sK4 = sK107(k2_zfmisc_1(sK2,sK3))
    | ~ r2_relset_1(sK2,sK3,sK107(k2_zfmisc_1(sK2,sK3)),sK4)
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3))
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f2951])).

fof(f2951,plain,(
    ! [X0] :
      ( m1_subset_1(sK107(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2374])).

fof(f2374,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK107(X0))
        & m1_subset_1(sK107(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK107])],[f1735,f2373])).

fof(f2373,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK107(X0))
        & m1_subset_1(sK107(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1735,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f489])).

fof(f489,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

fof(f4183,plain,
    ( ~ spl172_74
    | spl172_75
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4135,f3674,f4181,f4178])).

fof(f4181,plain,
    ( spl172_75
  <=> sK4 = sK105(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_75])])).

fof(f4135,plain,
    ( sK4 = sK105(k2_zfmisc_1(sK2,sK3))
    | ~ r2_relset_1(sK2,sK3,sK105(k2_zfmisc_1(sK2,sK3)),sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f2938])).

fof(f2938,plain,(
    ! [X0] : m1_subset_1(sK105(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2368])).

fof(f2368,plain,(
    ! [X0] :
      ( v1_xboole_0(sK105(X0))
      & m1_subset_1(sK105(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK105])],[f490,f2367])).

fof(f2367,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK105(X0))
        & m1_subset_1(sK105(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f490,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f4176,plain,
    ( ~ spl172_72
    | spl172_73
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4131,f3674,f4174,f4171])).

fof(f4171,plain,
    ( spl172_72
  <=> r2_relset_1(sK2,sK3,sK49(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_72])])).

fof(f4174,plain,
    ( spl172_73
  <=> sK4 = sK49(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_73])])).

fof(f4131,plain,
    ( sK4 = sK49(sK2,sK3)
    | ~ r2_relset_1(sK2,sK3,sK49(sK2,sK3),sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f2770])).

fof(f2770,plain,(
    ! [X0,X1] : m1_subset_1(sK49(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f2271])).

fof(f2271,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK49(X0,X1),X0,X1)
      & v1_funct_1(sK49(X0,X1))
      & v5_relat_1(sK49(X0,X1),X1)
      & v4_relat_1(sK49(X0,X1),X0)
      & v1_relat_1(sK49(X0,X1))
      & m1_subset_1(sK49(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49])],[f1480,f2270])).

fof(f2270,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK49(X0,X1),X0,X1)
        & v1_funct_1(sK49(X0,X1))
        & v5_relat_1(sK49(X0,X1),X1)
        & v4_relat_1(sK49(X0,X1),X0)
        & v1_relat_1(sK49(X0,X1))
        & m1_subset_1(sK49(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1480,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f4169,plain,
    ( ~ spl172_70
    | spl172_71
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4125,f3674,f4167,f4164])).

fof(f4167,plain,
    ( spl172_71
  <=> sK4 = sK9(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_71])])).

fof(f4125,plain,
    ( sK4 = sK9(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_relset_1(sK2,sK3,sK9(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))),sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f2583])).

fof(f2583,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f2180])).

fof(f2180,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f474,f2179])).

fof(f2179,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f474,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f4162,plain,
    ( spl172_67
    | spl172_69
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4118,f3674,f4160,f4153])).

fof(f4160,plain,
    ( spl172_69
  <=> ! [X20] :
        ( sK4 = k1_tarski(X20)
        | ~ m1_subset_1(X20,k2_zfmisc_1(sK2,sK3))
        | ~ r2_relset_1(sK2,sK3,k1_tarski(X20),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_69])])).

fof(f4118,plain,
    ( ! [X20] :
        ( sK4 = k1_tarski(X20)
        | ~ r2_relset_1(sK2,sK3,k1_tarski(X20),sK4)
        | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
        | ~ m1_subset_1(X20,k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f3183])).

fof(f3183,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f1898])).

fof(f1898,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f1897])).

fof(f1897,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f527])).

fof(f527,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f4158,plain,
    ( spl172_67
    | spl172_68
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4116,f3674,f4156,f4153])).

fof(f4156,plain,
    ( spl172_68
  <=> ! [X16,X17] :
        ( sK4 = k2_tarski(X16,X17)
        | ~ m1_subset_1(X16,k2_zfmisc_1(sK2,sK3))
        | ~ m1_subset_1(X17,k2_zfmisc_1(sK2,sK3))
        | ~ r2_relset_1(sK2,sK3,k2_tarski(X16,X17),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_68])])).

fof(f4116,plain,
    ( ! [X17,X16] :
        ( sK4 = k2_tarski(X16,X17)
        | ~ r2_relset_1(sK2,sK3,k2_tarski(X16,X17),sK4)
        | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
        | ~ m1_subset_1(X17,k2_zfmisc_1(sK2,sK3))
        | ~ m1_subset_1(X16,k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f3537])).

fof(f3537,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2159])).

fof(f2159,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          | k1_xboole_0 = X0
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f2158])).

fof(f2158,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          | k1_xboole_0 = X0
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f528])).

fof(f528,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(f4151,plain,
    ( ~ spl172_65
    | spl172_66
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4115,f3674,f4148,f4145])).

fof(f4145,plain,
    ( spl172_65
  <=> r2_relset_1(sK2,sK3,k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_65])])).

fof(f4148,plain,
    ( spl172_66
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_66])])).

fof(f4115,plain,
    ( k1_xboole_0 = sK4
    | ~ r2_relset_1(sK2,sK3,k1_xboole_0,sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f2916])).

fof(f2916,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f4150,plain,
    ( ~ spl172_65
    | spl172_66
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4114,f3674,f4148,f4145])).

fof(f4114,plain,
    ( k1_xboole_0 = sK4
    | ~ r2_relset_1(sK2,sK3,k1_xboole_0,sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f2626])).

fof(f2626,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

fof(f4143,plain,
    ( spl172_25
    | spl172_64
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f4111,f3674,f4141,f3797])).

fof(f3797,plain,
    ( spl172_25
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_25])])).

fof(f4141,plain,
    ( spl172_64
  <=> ! [X13] :
        ( sK4 = X13
        | ~ r2_hidden(X13,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ r2_relset_1(sK2,sK3,X13,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_64])])).

fof(f4111,plain,
    ( ! [X13] :
        ( sK4 = X13
        | ~ r2_relset_1(sK2,sK3,X13,sK4)
        | ~ r2_hidden(X13,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3677,f2934])).

fof(f2934,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2366])).

fof(f2366,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1723])).

fof(f1723,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f4103,plain,
    ( ~ spl172_7
    | ~ spl172_16
    | spl172_61 ),
    inference(avatar_contradiction_clause,[],[f4102])).

fof(f4102,plain,
    ( $false
    | ~ spl172_7
    | ~ spl172_16
    | spl172_61 ),
    inference(global_subsumption,[],[f3759,f3720,f4095])).

fof(f4095,plain,
    ( ~ v5_relat_1(sK4,sK3)
    | ~ v1_relat_1(sK4)
    | spl172_61 ),
    inference(resolution,[],[f4067,f3199])).

fof(f3199,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2441])).

fof(f2441,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1916])).

fof(f1916,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f4067,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | spl172_61 ),
    inference(avatar_component_clause,[],[f4066])).

fof(f4066,plain,
    ( spl172_61
  <=> r1_tarski(k2_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_61])])).

fof(f3759,plain,
    ( v5_relat_1(sK4,sK3)
    | ~ spl172_16 ),
    inference(avatar_component_clause,[],[f3758])).

fof(f3758,plain,
    ( spl172_16
  <=> v5_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_16])])).

fof(f4101,plain,
    ( ~ spl172_7
    | ~ spl172_16
    | spl172_61 ),
    inference(avatar_contradiction_clause,[],[f4100])).

fof(f4100,plain,
    ( $false
    | ~ spl172_7
    | ~ spl172_16
    | spl172_61 ),
    inference(global_subsumption,[],[f3759,f3720,f4095])).

fof(f4099,plain,
    ( ~ spl172_7
    | ~ spl172_16
    | spl172_61 ),
    inference(avatar_contradiction_clause,[],[f4098])).

fof(f4098,plain,
    ( $false
    | ~ spl172_7
    | ~ spl172_16
    | spl172_61 ),
    inference(global_subsumption,[],[f3759,f3720,f4095])).

fof(f4080,plain,
    ( ~ spl172_63
    | ~ spl172_7
    | ~ spl172_17
    | spl172_29 ),
    inference(avatar_split_clause,[],[f4076,f3819,f3762,f3719,f4078])).

fof(f3762,plain,
    ( spl172_17
  <=> r2_relset_1(sK2,sK3,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_17])])).

fof(f3819,plain,
    ( spl172_29
  <=> r2_relset_1(sK2,sK3,k5_relat_1(k6_relat_1(sK2),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_29])])).

fof(f4076,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK2)
    | ~ spl172_7
    | ~ spl172_17
    | spl172_29 ),
    inference(global_subsumption,[],[f3763,f3720,f4070])).

fof(f4070,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK4)
    | ~ r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4)
    | spl172_29 ),
    inference(superposition,[],[f3820,f2990])).

fof(f2990,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1764])).

fof(f1764,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1763])).

fof(f1763,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f869])).

fof(f869,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f3820,plain,
    ( ~ r2_relset_1(sK2,sK3,k5_relat_1(k6_relat_1(sK2),sK4),sK4)
    | spl172_29 ),
    inference(avatar_component_clause,[],[f3819])).

fof(f3763,plain,
    ( r2_relset_1(sK2,sK3,sK4,sK4)
    | ~ spl172_17 ),
    inference(avatar_component_clause,[],[f3762])).

fof(f4075,plain,
    ( ~ spl172_62
    | ~ spl172_7
    | spl172_29 ),
    inference(avatar_split_clause,[],[f4071,f3819,f3719,f4073])).

fof(f4073,plain,
    ( spl172_62
  <=> r2_relset_1(sK2,sK3,k7_relat_1(sK4,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_62])])).

fof(f4071,plain,
    ( ~ r2_relset_1(sK2,sK3,k7_relat_1(sK4,sK2),sK4)
    | ~ spl172_7
    | spl172_29 ),
    inference(global_subsumption,[],[f3720,f4069])).

fof(f4069,plain,
    ( ~ r2_relset_1(sK2,sK3,k7_relat_1(sK4,sK2),sK4)
    | ~ v1_relat_1(sK4)
    | spl172_29 ),
    inference(superposition,[],[f3820,f2994])).

fof(f2994,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1768])).

fof(f1768,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f883])).

fof(f883,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f4068,plain,
    ( ~ spl172_61
    | ~ spl172_7
    | ~ spl172_17
    | spl172_28 ),
    inference(avatar_split_clause,[],[f4064,f3813,f3762,f3719,f4066])).

fof(f3813,plain,
    ( spl172_28
  <=> r2_relset_1(sK2,sK3,k5_relat_1(sK4,k6_relat_1(sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_28])])).

fof(f4064,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ spl172_7
    | ~ spl172_17
    | spl172_28 ),
    inference(global_subsumption,[],[f3763,f3720,f4063])).

fof(f4063,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK4)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4)
    | spl172_28 ),
    inference(superposition,[],[f3814,f2991])).

fof(f2991,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1766])).

fof(f1766,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1765])).

fof(f1765,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f871])).

fof(f871,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f3814,plain,
    ( ~ r2_relset_1(sK2,sK3,k5_relat_1(sK4,k6_relat_1(sK3)),sK4)
    | spl172_28 ),
    inference(avatar_component_clause,[],[f3813])).

fof(f4062,plain,
    ( ~ spl172_19
    | spl172_60
    | ~ spl172_24 ),
    inference(avatar_split_clause,[],[f4058,f3793,f4060,f3773])).

fof(f3773,plain,
    ( spl172_19
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_19])])).

fof(f4060,plain,
    ( spl172_60
  <=> ! [X1,X0] :
        ( v4_relat_1(sK4,X0)
        | ~ v4_relat_1(k2_zfmisc_1(sK2,sK3),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_60])])).

fof(f3793,plain,
    ( spl172_24
  <=> ! [X17] :
        ( v4_relat_1(sK4,X17)
        | ~ v4_relat_1(k2_zfmisc_1(sK2,sK3),X17) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_24])])).

fof(f4058,plain,
    ( ! [X0,X1] :
        ( v4_relat_1(sK4,X0)
        | ~ v4_relat_1(k2_zfmisc_1(sK2,sK3),X1)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | ~ r1_tarski(X1,X0) )
    | ~ spl172_24 ),
    inference(resolution,[],[f3794,f3234])).

fof(f3234,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1931])).

fof(f1931,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1930])).

fof(f1930,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f822])).

fof(f822,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f3794,plain,
    ( ! [X17] :
        ( ~ v4_relat_1(k2_zfmisc_1(sK2,sK3),X17)
        | v4_relat_1(sK4,X17) )
    | ~ spl172_24 ),
    inference(avatar_component_clause,[],[f3793])).

fof(f4057,plain,
    ( ~ spl172_19
    | spl172_59
    | ~ spl172_23 ),
    inference(avatar_split_clause,[],[f4053,f3789,f4055,f3773])).

fof(f4055,plain,
    ( spl172_59
  <=> ! [X1,X0] :
        ( v5_relat_1(sK4,X0)
        | ~ v5_relat_1(k2_zfmisc_1(sK2,sK3),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_59])])).

fof(f3789,plain,
    ( spl172_23
  <=> ! [X16] :
        ( v5_relat_1(sK4,X16)
        | ~ v5_relat_1(k2_zfmisc_1(sK2,sK3),X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_23])])).

fof(f4053,plain,
    ( ! [X0,X1] :
        ( v5_relat_1(sK4,X0)
        | ~ v5_relat_1(k2_zfmisc_1(sK2,sK3),X1)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | ~ r1_tarski(X1,X0) )
    | ~ spl172_23 ),
    inference(resolution,[],[f3790,f3198])).

fof(f3198,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1915])).

fof(f1915,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1914])).

fof(f1914,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f823])).

fof(f823,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

fof(f3790,plain,
    ( ! [X16] :
        ( ~ v5_relat_1(k2_zfmisc_1(sK2,sK3),X16)
        | v5_relat_1(sK4,X16) )
    | ~ spl172_23 ),
    inference(avatar_component_clause,[],[f3789])).

fof(f4052,plain,
    ( ~ spl172_19
    | spl172_58
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3940,f3674,f4050,f3773])).

fof(f4050,plain,
    ( spl172_58
  <=> ! [X96,X97] :
        ( ~ r2_hidden(k4_tarski(sK119(X96,X97,k2_zfmisc_1(sK2,sK3)),sK120(X96,X97,k2_zfmisc_1(sK2,sK3))),sK4)
        | ~ v1_relat_1(X96)
        | k2_zfmisc_1(sK2,sK3) = k7_relat_1(X96,X97)
        | ~ r2_hidden(sK119(X96,X97,k2_zfmisc_1(sK2,sK3)),X97)
        | ~ r2_hidden(k4_tarski(sK119(X96,X97,k2_zfmisc_1(sK2,sK3)),sK120(X96,X97,k2_zfmisc_1(sK2,sK3))),X96) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_58])])).

fof(f3940,plain,
    ( ! [X97,X96] :
        ( ~ r2_hidden(k4_tarski(sK119(X96,X97,k2_zfmisc_1(sK2,sK3)),sK120(X96,X97,k2_zfmisc_1(sK2,sK3))),sK4)
        | ~ r2_hidden(k4_tarski(sK119(X96,X97,k2_zfmisc_1(sK2,sK3)),sK120(X96,X97,k2_zfmisc_1(sK2,sK3))),X96)
        | ~ r2_hidden(sK119(X96,X97,k2_zfmisc_1(sK2,sK3)),X97)
        | k2_zfmisc_1(sK2,sK3) = k7_relat_1(X96,X97)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | ~ v1_relat_1(X96) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f3109])).

fof(f3109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X0)
      | ~ r2_hidden(sK119(X0,X1,X2),X1)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2418])).

fof(f2418,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK119(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X0)
                    & r2_hidden(sK119(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK119,sK120])],[f2416,f2417])).

fof(f2417,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X0)
          | ~ r2_hidden(sK119(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X0)
            & r2_hidden(sK119(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK119(X0,X1,X2),sK120(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2416,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2415])).

fof(f2415,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2414])).

fof(f2414,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1858])).

fof(f1858,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f3698,plain,
    ( ! [X14] :
        ( r2_hidden(X14,k2_zfmisc_1(sK2,sK3))
        | ~ r2_hidden(X14,sK4) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2602])).

fof(f2602,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1543])).

fof(f1543,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f4048,plain,
    ( ~ spl172_19
    | spl172_57
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3939,f3674,f4046,f3773])).

fof(f4046,plain,
    ( spl172_57
  <=> ! [X93,X95,X94] :
        ( ~ r2_hidden(k4_tarski(sK96(X93,X94,k2_zfmisc_1(sK2,sK3)),sK97(X93,X94,k2_zfmisc_1(sK2,sK3))),sK4)
        | ~ v1_relat_1(X93)
        | ~ v1_relat_1(X94)
        | k2_zfmisc_1(sK2,sK3) = k5_relat_1(X93,X94)
        | ~ r2_hidden(k4_tarski(sK96(X93,X94,k2_zfmisc_1(sK2,sK3)),X95),X93)
        | ~ r2_hidden(k4_tarski(X95,sK97(X93,X94,k2_zfmisc_1(sK2,sK3))),X94) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_57])])).

fof(f3939,plain,
    ( ! [X94,X95,X93] :
        ( ~ r2_hidden(k4_tarski(sK96(X93,X94,k2_zfmisc_1(sK2,sK3)),sK97(X93,X94,k2_zfmisc_1(sK2,sK3))),sK4)
        | ~ r2_hidden(k4_tarski(X95,sK97(X93,X94,k2_zfmisc_1(sK2,sK3))),X94)
        | ~ r2_hidden(k4_tarski(sK96(X93,X94,k2_zfmisc_1(sK2,sK3)),X95),X93)
        | k2_zfmisc_1(sK2,sK3) = k5_relat_1(X93,X94)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | ~ v1_relat_1(X94)
        | ~ v1_relat_1(X93) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2897])).

fof(f2897,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK96(X0,X1,X2),sK97(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(X5,sK97(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK96(X0,X1,X2),X5),X0)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2355])).

fof(f2355,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK97(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK96(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK96(X0,X1,X2),sK97(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK98(X0,X1,X2),sK97(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK96(X0,X1,X2),sK98(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK96(X0,X1,X2),sK97(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK99(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK99(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96,sK97,sK98,sK99])],[f2351,f2354,f2353,f2352])).

fof(f2352,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK97(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK96(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK96(X0,X1,X2),sK97(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK97(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK96(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK96(X0,X1,X2),sK97(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2353,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK97(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK96(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK98(X0,X1,X2),sK97(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK96(X0,X1,X2),sK98(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2354,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK99(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK99(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2351,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2350])).

fof(f2350,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1685])).

fof(f1685,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f660])).

fof(f660,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f4044,plain,
    ( ~ spl172_19
    | spl172_56
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3938,f3674,f4042,f3773])).

fof(f4042,plain,
    ( spl172_56
  <=> ! [X91,X90,X92] :
        ( ~ r2_hidden(k4_tarski(X90,sK30(X91,k2_zfmisc_1(sK2,sK3),X90)),sK4)
        | v1_xboole_0(X91)
        | sP1(k2_zfmisc_1(sK2,sK3),X91)
        | ~ r2_hidden(X90,sK29(X91,k2_zfmisc_1(sK2,sK3)))
        | r2_hidden(k1_funct_1(sK28(X91,k2_zfmisc_1(sK2,sK3)),X92),X92)
        | ~ r2_hidden(X92,X91) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_56])])).

fof(f3938,plain,
    ( ! [X92,X90,X91] :
        ( ~ r2_hidden(k4_tarski(X90,sK30(X91,k2_zfmisc_1(sK2,sK3),X90)),sK4)
        | ~ r2_hidden(X92,X91)
        | r2_hidden(k1_funct_1(sK28(X91,k2_zfmisc_1(sK2,sK3)),X92),X92)
        | ~ r2_hidden(X90,sK29(X91,k2_zfmisc_1(sK2,sK3)))
        | sP1(k2_zfmisc_1(sK2,sK3),X91)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X91) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2692])).

fof(f2692,plain,(
    ! [X6,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK30(X0,X1,X6)),X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k1_funct_1(sK28(X0,X1),X3),X3)
      | ~ r2_hidden(X6,sK29(X0,X1))
      | sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2229])).

fof(f2229,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ( ! [X4] :
                  ( r2_hidden(k4_tarski(k1_funct_1(sK28(X0,X1),X3),X4),X1)
                  | ~ r2_hidden(X4,X3) )
              & r2_hidden(k1_funct_1(sK28(X0,X1),X3),X3) )
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK28(X0,X1)) = X0
        & v1_funct_1(sK28(X0,X1))
        & v1_relat_1(sK28(X0,X1)) )
      | ( ! [X6] :
            ( ( ~ r2_hidden(k4_tarski(X6,sK30(X0,X1,X6)),X1)
              & r2_hidden(sK30(X0,X1,X6),sK29(X0,X1)) )
            | ~ r2_hidden(X6,sK29(X0,X1)) )
        & r2_hidden(sK29(X0,X1),X0) )
      | sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f2225,f2228,f2227,f2226])).

fof(f2226,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ( ! [X4] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),X4),X1)
                    | ~ r2_hidden(X4,X3) )
                & r2_hidden(k1_funct_1(X2,X3),X3) )
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( ( ! [X4] :
                  ( r2_hidden(k4_tarski(k1_funct_1(sK28(X0,X1),X3),X4),X1)
                  | ~ r2_hidden(X4,X3) )
              & r2_hidden(k1_funct_1(sK28(X0,X1),X3),X3) )
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK28(X0,X1)) = X0
        & v1_funct_1(sK28(X0,X1))
        & v1_relat_1(sK28(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2227,plain,(
    ! [X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( ? [X7] :
                  ( ~ r2_hidden(k4_tarski(X6,X7),X1)
                  & r2_hidden(X7,X5) )
              | ~ r2_hidden(X6,X5) )
          & r2_hidden(X5,X0) )
     => ( ! [X6] :
            ( ? [X7] :
                ( ~ r2_hidden(k4_tarski(X6,X7),X1)
                & r2_hidden(X7,sK29(X0,X1)) )
            | ~ r2_hidden(X6,sK29(X0,X1)) )
        & r2_hidden(sK29(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2228,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r2_hidden(k4_tarski(X6,X7),X1)
          & r2_hidden(X7,sK29(X0,X1)) )
     => ( ~ r2_hidden(k4_tarski(X6,sK30(X0,X1,X6)),X1)
        & r2_hidden(sK30(X0,X1,X6),sK29(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2225,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ( ! [X4] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),X4),X1)
                    | ~ r2_hidden(X4,X3) )
                & r2_hidden(k1_funct_1(X2,X3),X3) )
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ? [X5] :
          ( ! [X6] :
              ( ? [X7] :
                  ( ~ r2_hidden(k4_tarski(X6,X7),X1)
                  & r2_hidden(X7,X5) )
              | ~ r2_hidden(X6,X5) )
          & r2_hidden(X5,X0) )
      | sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f2163])).

fof(f2163,plain,(
    ! [X0,X1] :
      ( ? [X10] :
          ( ! [X11] :
              ( ( ! [X12] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1)
                    | ~ r2_hidden(X12,X11) )
                & r2_hidden(k1_funct_1(X10,X11),X11) )
              | ~ r2_hidden(X11,X0) )
          & k1_relat_1(X10) = X0
          & v1_funct_1(X10)
          & v1_relat_1(X10) )
      | ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & r2_hidden(X2,X0) )
      | sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f1598,f2162])).

fof(f2162,plain,(
    ! [X1,X0] :
      ( ? [X5,X6,X7] :
          ( X6 != X7
          & ! [X8] :
              ( r2_hidden(k4_tarski(X7,X8),X1)
              | ~ r2_hidden(X8,X5) )
          & r2_hidden(X7,X5)
          & ! [X9] :
              ( r2_hidden(k4_tarski(X6,X9),X1)
              | ~ r2_hidden(X9,X5) )
          & r2_hidden(X6,X5)
          & r2_hidden(X5,X0) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1598,plain,(
    ! [X0,X1] :
      ( ? [X10] :
          ( ! [X11] :
              ( ( ! [X12] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1)
                    | ~ r2_hidden(X12,X11) )
                & r2_hidden(k1_funct_1(X10,X11),X11) )
              | ~ r2_hidden(X11,X0) )
          & k1_relat_1(X10) = X0
          & v1_funct_1(X10)
          & v1_relat_1(X10) )
      | ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & r2_hidden(X2,X0) )
      | ? [X5,X6,X7] :
          ( X6 != X7
          & ! [X8] :
              ( r2_hidden(k4_tarski(X7,X8),X1)
              | ~ r2_hidden(X8,X5) )
          & r2_hidden(X7,X5)
          & ! [X9] :
              ( r2_hidden(k4_tarski(X6,X9),X1)
              | ~ r2_hidden(X9,X5) )
          & r2_hidden(X6,X5)
          & r2_hidden(X5,X0) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1597])).

fof(f1597,plain,(
    ! [X0,X1] :
      ( ? [X10] :
          ( ! [X11] :
              ( ( ! [X12] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1)
                    | ~ r2_hidden(X12,X11) )
                & r2_hidden(k1_funct_1(X10,X11),X11) )
              | ~ r2_hidden(X11,X0) )
          & k1_relat_1(X10) = X0
          & v1_funct_1(X10)
          & v1_relat_1(X10) )
      | ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & r2_hidden(X2,X0) )
      | ? [X5,X6,X7] :
          ( X6 != X7
          & ! [X8] :
              ( r2_hidden(k4_tarski(X7,X8),X1)
              | ~ r2_hidden(X8,X5) )
          & r2_hidden(X7,X5)
          & ! [X9] :
              ( r2_hidden(k4_tarski(X6,X9),X1)
              | ~ r2_hidden(X9,X5) )
          & r2_hidden(X6,X5)
          & r2_hidden(X5,X0) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1506])).

fof(f1506,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ( ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( ! [X4] :
                          ( r2_hidden(X4,X2)
                         => r2_hidden(k4_tarski(X3,X4),X1) )
                      & r2_hidden(X3,X2) )
                & r2_hidden(X2,X0) )
          & ! [X5,X6,X7] :
              ( ( ! [X8] :
                    ( r2_hidden(X8,X5)
                   => r2_hidden(k4_tarski(X7,X8),X1) )
                & r2_hidden(X7,X5)
                & ! [X9] :
                    ( r2_hidden(X9,X5)
                   => r2_hidden(k4_tarski(X6,X9),X1) )
                & r2_hidden(X6,X5)
                & r2_hidden(X5,X0) )
             => X6 = X7 ) )
       => ? [X10] :
            ( ! [X11] :
                ( r2_hidden(X11,X0)
               => ( ! [X12] :
                      ( r2_hidden(X12,X11)
                     => r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1) )
                  & r2_hidden(k1_funct_1(X10,X11),X11) ) )
            & k1_relat_1(X10) = X0
            & v1_funct_1(X10)
            & v1_relat_1(X10) ) ) ) ),
    inference(rectify,[],[f1440])).

fof(f1440,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ( ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( ! [X7] :
                          ( r2_hidden(X7,X2)
                         => r2_hidden(k4_tarski(X3,X7),X1) )
                      & r2_hidden(X3,X2) )
                & r2_hidden(X2,X0) )
          & ! [X2,X3,X4] :
              ( ( ! [X6] :
                    ( r2_hidden(X6,X2)
                   => r2_hidden(k4_tarski(X4,X6),X1) )
                & r2_hidden(X4,X2)
                & ! [X5] :
                    ( r2_hidden(X5,X2)
                   => r2_hidden(k4_tarski(X3,X5),X1) )
                & r2_hidden(X3,X2)
                & r2_hidden(X2,X0) )
             => X3 = X4 ) )
       => ? [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X0)
               => ( ! [X8] :
                      ( r2_hidden(X8,X3)
                     => r2_hidden(k4_tarski(k1_funct_1(X2,X3),X8),X1) )
                  & r2_hidden(k1_funct_1(X2,X3),X3) ) )
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s2_funct_1__e11_32__wellord2)).

fof(f4040,plain,
    ( ~ spl172_19
    | spl172_55
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3937,f3674,f4038,f3773])).

fof(f4038,plain,
    ( spl172_55
  <=> ! [X89,X88] :
        ( ~ r2_hidden(k4_tarski(X88,sK30(X89,k2_zfmisc_1(sK2,sK3),X88)),sK4)
        | v1_xboole_0(X89)
        | sP1(k2_zfmisc_1(sK2,sK3),X89)
        | ~ r2_hidden(X88,sK29(X89,k2_zfmisc_1(sK2,sK3)))
        | k1_relat_1(sK28(X89,k2_zfmisc_1(sK2,sK3))) = X89 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_55])])).

fof(f3937,plain,
    ( ! [X88,X89] :
        ( ~ r2_hidden(k4_tarski(X88,sK30(X89,k2_zfmisc_1(sK2,sK3),X88)),sK4)
        | k1_relat_1(sK28(X89,k2_zfmisc_1(sK2,sK3))) = X89
        | ~ r2_hidden(X88,sK29(X89,k2_zfmisc_1(sK2,sK3)))
        | sP1(k2_zfmisc_1(sK2,sK3),X89)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X89) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2689])).

fof(f2689,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK30(X0,X1,X6)),X1)
      | k1_relat_1(sK28(X0,X1)) = X0
      | ~ r2_hidden(X6,sK29(X0,X1))
      | sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2229])).

fof(f4036,plain,
    ( ~ spl172_19
    | spl172_54
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3936,f3674,f4034,f3773])).

fof(f4034,plain,
    ( spl172_54
  <=> ! [X86,X87] :
        ( ~ r2_hidden(k4_tarski(X86,sK30(X87,k2_zfmisc_1(sK2,sK3),X86)),sK4)
        | v1_xboole_0(X87)
        | sP1(k2_zfmisc_1(sK2,sK3),X87)
        | ~ r2_hidden(X86,sK29(X87,k2_zfmisc_1(sK2,sK3)))
        | v1_funct_1(sK28(X87,k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_54])])).

fof(f3936,plain,
    ( ! [X87,X86] :
        ( ~ r2_hidden(k4_tarski(X86,sK30(X87,k2_zfmisc_1(sK2,sK3),X86)),sK4)
        | v1_funct_1(sK28(X87,k2_zfmisc_1(sK2,sK3)))
        | ~ r2_hidden(X86,sK29(X87,k2_zfmisc_1(sK2,sK3)))
        | sP1(k2_zfmisc_1(sK2,sK3),X87)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X87) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2686])).

fof(f2686,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK30(X0,X1,X6)),X1)
      | v1_funct_1(sK28(X0,X1))
      | ~ r2_hidden(X6,sK29(X0,X1))
      | sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2229])).

fof(f4032,plain,
    ( ~ spl172_19
    | spl172_53
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3935,f3674,f4030,f3773])).

fof(f4030,plain,
    ( spl172_53
  <=> ! [X84,X85] :
        ( ~ r2_hidden(k4_tarski(X84,sK30(X85,k2_zfmisc_1(sK2,sK3),X84)),sK4)
        | v1_xboole_0(X85)
        | sP1(k2_zfmisc_1(sK2,sK3),X85)
        | ~ r2_hidden(X84,sK29(X85,k2_zfmisc_1(sK2,sK3)))
        | v1_relat_1(sK28(X85,k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_53])])).

fof(f3935,plain,
    ( ! [X85,X84] :
        ( ~ r2_hidden(k4_tarski(X84,sK30(X85,k2_zfmisc_1(sK2,sK3),X84)),sK4)
        | v1_relat_1(sK28(X85,k2_zfmisc_1(sK2,sK3)))
        | ~ r2_hidden(X84,sK29(X85,k2_zfmisc_1(sK2,sK3)))
        | sP1(k2_zfmisc_1(sK2,sK3),X85)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X85) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2683])).

fof(f2683,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK30(X0,X1,X6)),X1)
      | v1_relat_1(sK28(X0,X1))
      | ~ r2_hidden(X6,sK29(X0,X1))
      | sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2229])).

fof(f4028,plain,
    ( ~ spl172_19
    | spl172_52
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3934,f3674,f4026,f3773])).

fof(f4026,plain,
    ( spl172_52
  <=> ! [X82,X81,X83] :
        ( ~ r2_hidden(k4_tarski(X81,sK24(X82,k2_zfmisc_1(sK2,sK3),X81)),sK4)
        | v1_xboole_0(X82)
        | sP0(k2_zfmisc_1(sK2,sK3),X82)
        | ~ r2_hidden(X81,sK23(X82,k2_zfmisc_1(sK2,sK3)))
        | r2_hidden(k1_funct_1(sK22(X82,k2_zfmisc_1(sK2,sK3)),X83),X83)
        | ~ r2_hidden(X83,X82) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_52])])).

fof(f3934,plain,
    ( ! [X83,X81,X82] :
        ( ~ r2_hidden(k4_tarski(X81,sK24(X82,k2_zfmisc_1(sK2,sK3),X81)),sK4)
        | ~ r2_hidden(X83,X82)
        | r2_hidden(k1_funct_1(sK22(X82,k2_zfmisc_1(sK2,sK3)),X83),X83)
        | ~ r2_hidden(X81,sK23(X82,k2_zfmisc_1(sK2,sK3)))
        | sP0(k2_zfmisc_1(sK2,sK3),X82)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X82) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2671])).

fof(f2671,plain,(
    ! [X6,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK24(X0,X1,X6)),X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k1_funct_1(sK22(X0,X1),X3),X3)
      | ~ r2_hidden(X6,sK23(X0,X1))
      | sP0(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2220])).

fof(f2220,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ( ! [X4] :
                  ( r2_hidden(k4_tarski(k1_funct_1(sK22(X0,X1),X3),X4),X1)
                  | ~ r2_hidden(X4,X3) )
              & r2_hidden(k1_funct_1(sK22(X0,X1),X3),X3) )
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK22(X0,X1)) = X0
        & v1_funct_1(sK22(X0,X1))
        & v1_relat_1(sK22(X0,X1)) )
      | ( ! [X6] :
            ( ( ~ r2_hidden(k4_tarski(X6,sK24(X0,X1,X6)),X1)
              & r2_hidden(sK24(X0,X1,X6),sK23(X0,X1)) )
            | ~ r2_hidden(X6,sK23(X0,X1)) )
        & r2_hidden(sK23(X0,X1),X0) )
      | sP0(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23,sK24])],[f2216,f2219,f2218,f2217])).

fof(f2217,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ( ! [X4] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),X4),X1)
                    | ~ r2_hidden(X4,X3) )
                & r2_hidden(k1_funct_1(X2,X3),X3) )
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( ( ! [X4] :
                  ( r2_hidden(k4_tarski(k1_funct_1(sK22(X0,X1),X3),X4),X1)
                  | ~ r2_hidden(X4,X3) )
              & r2_hidden(k1_funct_1(sK22(X0,X1),X3),X3) )
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK22(X0,X1)) = X0
        & v1_funct_1(sK22(X0,X1))
        & v1_relat_1(sK22(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2218,plain,(
    ! [X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( ? [X7] :
                  ( ~ r2_hidden(k4_tarski(X6,X7),X1)
                  & r2_hidden(X7,X5) )
              | ~ r2_hidden(X6,X5) )
          & r2_hidden(X5,X0) )
     => ( ! [X6] :
            ( ? [X7] :
                ( ~ r2_hidden(k4_tarski(X6,X7),X1)
                & r2_hidden(X7,sK23(X0,X1)) )
            | ~ r2_hidden(X6,sK23(X0,X1)) )
        & r2_hidden(sK23(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2219,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r2_hidden(k4_tarski(X6,X7),X1)
          & r2_hidden(X7,sK23(X0,X1)) )
     => ( ~ r2_hidden(k4_tarski(X6,sK24(X0,X1,X6)),X1)
        & r2_hidden(sK24(X0,X1,X6),sK23(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2216,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ( ! [X4] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),X4),X1)
                    | ~ r2_hidden(X4,X3) )
                & r2_hidden(k1_funct_1(X2,X3),X3) )
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ? [X5] :
          ( ! [X6] :
              ( ? [X7] :
                  ( ~ r2_hidden(k4_tarski(X6,X7),X1)
                  & r2_hidden(X7,X5) )
              | ~ r2_hidden(X6,X5) )
          & r2_hidden(X5,X0) )
      | sP0(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f2161])).

fof(f2161,plain,(
    ! [X0,X1] :
      ( ? [X10] :
          ( ! [X11] :
              ( ( ! [X12] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1)
                    | ~ r2_hidden(X12,X11) )
                & r2_hidden(k1_funct_1(X10,X11),X11) )
              | ~ r2_hidden(X11,X0) )
          & k1_relat_1(X10) = X0
          & v1_funct_1(X10)
          & v1_relat_1(X10) )
      | ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & r2_hidden(X2,X0) )
      | sP0(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f1596,f2160])).

fof(f2160,plain,(
    ! [X1,X0] :
      ( ? [X5,X6,X7] :
          ( X6 != X7
          & ! [X8] :
              ( r2_hidden(k4_tarski(X7,X8),X1)
              | ~ r2_hidden(X8,X5) )
          & r2_hidden(X7,X5)
          & ! [X9] :
              ( r2_hidden(k4_tarski(X6,X9),X1)
              | ~ r2_hidden(X9,X5) )
          & r2_hidden(X6,X5)
          & r2_hidden(X5,X0) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1596,plain,(
    ! [X0,X1] :
      ( ? [X10] :
          ( ! [X11] :
              ( ( ! [X12] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1)
                    | ~ r2_hidden(X12,X11) )
                & r2_hidden(k1_funct_1(X10,X11),X11) )
              | ~ r2_hidden(X11,X0) )
          & k1_relat_1(X10) = X0
          & v1_funct_1(X10)
          & v1_relat_1(X10) )
      | ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & r2_hidden(X2,X0) )
      | ? [X5,X6,X7] :
          ( X6 != X7
          & ! [X8] :
              ( r2_hidden(k4_tarski(X7,X8),X1)
              | ~ r2_hidden(X8,X5) )
          & r2_hidden(X7,X5)
          & ! [X9] :
              ( r2_hidden(k4_tarski(X6,X9),X1)
              | ~ r2_hidden(X9,X5) )
          & r2_hidden(X6,X5)
          & r2_hidden(X5,X0) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1595])).

fof(f1595,plain,(
    ! [X0,X1] :
      ( ? [X10] :
          ( ! [X11] :
              ( ( ! [X12] :
                    ( r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1)
                    | ~ r2_hidden(X12,X11) )
                & r2_hidden(k1_funct_1(X10,X11),X11) )
              | ~ r2_hidden(X11,X0) )
          & k1_relat_1(X10) = X0
          & v1_funct_1(X10)
          & v1_relat_1(X10) )
      | ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & r2_hidden(X2,X0) )
      | ? [X5,X6,X7] :
          ( X6 != X7
          & ! [X8] :
              ( r2_hidden(k4_tarski(X7,X8),X1)
              | ~ r2_hidden(X8,X5) )
          & r2_hidden(X7,X5)
          & ! [X9] :
              ( r2_hidden(k4_tarski(X6,X9),X1)
              | ~ r2_hidden(X9,X5) )
          & r2_hidden(X6,X5)
          & r2_hidden(X5,X0) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1505])).

fof(f1505,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ( ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( ! [X4] :
                          ( r2_hidden(X4,X2)
                         => r2_hidden(k4_tarski(X3,X4),X1) )
                      & r2_hidden(X3,X2) )
                & r2_hidden(X2,X0) )
          & ! [X5,X6,X7] :
              ( ( ! [X8] :
                    ( r2_hidden(X8,X5)
                   => r2_hidden(k4_tarski(X7,X8),X1) )
                & r2_hidden(X7,X5)
                & ! [X9] :
                    ( r2_hidden(X9,X5)
                   => r2_hidden(k4_tarski(X6,X9),X1) )
                & r2_hidden(X6,X5)
                & r2_hidden(X5,X0) )
             => X6 = X7 ) )
       => ? [X10] :
            ( ! [X11] :
                ( r2_hidden(X11,X0)
               => ( ! [X12] :
                      ( r2_hidden(X12,X11)
                     => r2_hidden(k4_tarski(k1_funct_1(X10,X11),X12),X1) )
                  & r2_hidden(k1_funct_1(X10,X11),X11) ) )
            & k1_relat_1(X10) = X0
            & v1_funct_1(X10)
            & v1_relat_1(X10) ) ) ) ),
    inference(rectify,[],[f1439])).

fof(f1439,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ( ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( ! [X7] :
                          ( r2_hidden(X7,X2)
                         => r2_hidden(k4_tarski(X3,X7),X1) )
                      & r2_hidden(X3,X2) )
                & r2_hidden(X2,X0) )
          & ! [X2,X3,X4] :
              ( ( ! [X6] :
                    ( r2_hidden(X6,X2)
                   => r2_hidden(k4_tarski(X4,X6),X1) )
                & r2_hidden(X4,X2)
                & ! [X5] :
                    ( r2_hidden(X5,X2)
                   => r2_hidden(k4_tarski(X3,X5),X1) )
                & r2_hidden(X3,X2)
                & r2_hidden(X2,X0) )
             => X3 = X4 ) )
       => ? [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X0)
               => ( ! [X8] :
                      ( r2_hidden(X8,X3)
                     => r2_hidden(k4_tarski(k1_funct_1(X2,X3),X8),X1) )
                  & r2_hidden(k1_funct_1(X2,X3),X3) ) )
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s2_funct_1__e10_33__wellord2)).

fof(f4024,plain,
    ( ~ spl172_19
    | spl172_51
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3933,f3674,f4022,f3773])).

fof(f4022,plain,
    ( spl172_51
  <=> ! [X79,X80] :
        ( ~ r2_hidden(k4_tarski(X79,sK24(X80,k2_zfmisc_1(sK2,sK3),X79)),sK4)
        | v1_xboole_0(X80)
        | sP0(k2_zfmisc_1(sK2,sK3),X80)
        | ~ r2_hidden(X79,sK23(X80,k2_zfmisc_1(sK2,sK3)))
        | k1_relat_1(sK22(X80,k2_zfmisc_1(sK2,sK3))) = X80 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_51])])).

fof(f3933,plain,
    ( ! [X80,X79] :
        ( ~ r2_hidden(k4_tarski(X79,sK24(X80,k2_zfmisc_1(sK2,sK3),X79)),sK4)
        | k1_relat_1(sK22(X80,k2_zfmisc_1(sK2,sK3))) = X80
        | ~ r2_hidden(X79,sK23(X80,k2_zfmisc_1(sK2,sK3)))
        | sP0(k2_zfmisc_1(sK2,sK3),X80)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X80) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2668])).

fof(f2668,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK24(X0,X1,X6)),X1)
      | k1_relat_1(sK22(X0,X1)) = X0
      | ~ r2_hidden(X6,sK23(X0,X1))
      | sP0(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2220])).

fof(f4020,plain,
    ( ~ spl172_19
    | spl172_50
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3932,f3674,f4018,f3773])).

fof(f4018,plain,
    ( spl172_50
  <=> ! [X77,X78] :
        ( ~ r2_hidden(k4_tarski(X77,sK24(X78,k2_zfmisc_1(sK2,sK3),X77)),sK4)
        | v1_xboole_0(X78)
        | sP0(k2_zfmisc_1(sK2,sK3),X78)
        | ~ r2_hidden(X77,sK23(X78,k2_zfmisc_1(sK2,sK3)))
        | v1_funct_1(sK22(X78,k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_50])])).

fof(f3932,plain,
    ( ! [X78,X77] :
        ( ~ r2_hidden(k4_tarski(X77,sK24(X78,k2_zfmisc_1(sK2,sK3),X77)),sK4)
        | v1_funct_1(sK22(X78,k2_zfmisc_1(sK2,sK3)))
        | ~ r2_hidden(X77,sK23(X78,k2_zfmisc_1(sK2,sK3)))
        | sP0(k2_zfmisc_1(sK2,sK3),X78)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X78) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2665])).

fof(f2665,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK24(X0,X1,X6)),X1)
      | v1_funct_1(sK22(X0,X1))
      | ~ r2_hidden(X6,sK23(X0,X1))
      | sP0(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2220])).

fof(f4016,plain,
    ( ~ spl172_19
    | spl172_49
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3931,f3674,f4014,f3773])).

fof(f4014,plain,
    ( spl172_49
  <=> ! [X75,X76] :
        ( ~ r2_hidden(k4_tarski(X75,sK24(X76,k2_zfmisc_1(sK2,sK3),X75)),sK4)
        | v1_xboole_0(X76)
        | sP0(k2_zfmisc_1(sK2,sK3),X76)
        | ~ r2_hidden(X75,sK23(X76,k2_zfmisc_1(sK2,sK3)))
        | v1_relat_1(sK22(X76,k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_49])])).

fof(f3931,plain,
    ( ! [X76,X75] :
        ( ~ r2_hidden(k4_tarski(X75,sK24(X76,k2_zfmisc_1(sK2,sK3),X75)),sK4)
        | v1_relat_1(sK22(X76,k2_zfmisc_1(sK2,sK3)))
        | ~ r2_hidden(X75,sK23(X76,k2_zfmisc_1(sK2,sK3)))
        | sP0(k2_zfmisc_1(sK2,sK3),X76)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | v1_xboole_0(X76) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2662])).

fof(f2662,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X6,sK24(X0,X1,X6)),X1)
      | v1_relat_1(sK22(X0,X1))
      | ~ r2_hidden(X6,sK23(X0,X1))
      | sP0(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2220])).

fof(f4012,plain,
    ( ~ spl172_19
    | spl172_48
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3927,f3674,f4010,f3773])).

fof(f4010,plain,
    ( spl172_48
  <=> ! [X67,X66] :
        ( ~ r2_hidden(k4_tarski(X66,X67),sK4)
        | r2_hidden(X67,k2_relat_1(k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_48])])).

fof(f3927,plain,
    ( ! [X66,X67] :
        ( ~ r2_hidden(k4_tarski(X66,X67),sK4)
        | r2_hidden(X67,k2_relat_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2832])).

fof(f2832,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1655])).

fof(f1655,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1654])).

fof(f1654,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f814])).

fof(f814,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f4008,plain,
    ( ~ spl172_19
    | spl172_47
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3926,f3674,f4006,f3773])).

fof(f4006,plain,
    ( spl172_47
  <=> ! [X65,X64] :
        ( ~ r2_hidden(k4_tarski(X64,X65),sK4)
        | r2_hidden(X64,k1_relat_1(k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_47])])).

fof(f3926,plain,
    ( ! [X64,X65] :
        ( ~ r2_hidden(k4_tarski(X64,X65),sK4)
        | r2_hidden(X64,k1_relat_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2831])).

fof(f2831,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1655])).

fof(f4004,plain,
    ( ~ spl172_19
    | spl172_46
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3922,f3674,f4002,f3773])).

fof(f4002,plain,
    ( spl172_46
  <=> ! [X57] :
        ( ~ r2_hidden(k4_tarski(sK111(X57,k2_zfmisc_1(sK2,sK3)),sK111(X57,k2_zfmisc_1(sK2,sK3))),sK4)
        | r1_tarski(k6_relat_1(X57),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_46])])).

fof(f3922,plain,
    ( ! [X57] :
        ( ~ r2_hidden(k4_tarski(sK111(X57,k2_zfmisc_1(sK2,sK3)),sK111(X57,k2_zfmisc_1(sK2,sK3))),sK4)
        | r1_tarski(k6_relat_1(X57),k2_zfmisc_1(sK2,sK3))
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2989])).

fof(f2989,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK111(X0,X1),sK111(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2392])).

fof(f2392,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK111(X0,X1),sK111(X0,X1)),X1)
        & r2_hidden(sK111(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK111])],[f1762,f2391])).

fof(f2391,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK111(X0,X1),sK111(X0,X1)),X1)
        & r2_hidden(sK111(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1762,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1761])).

fof(f1761,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f865])).

fof(f865,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(f4000,plain,
    ( ~ spl172_19
    | spl172_45
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3921,f3674,f3998,f3773])).

fof(f3998,plain,
    ( spl172_45
  <=> ! [X56] :
        ( ~ r2_hidden(k4_tarski(sK109(X56,k2_zfmisc_1(sK2,sK3)),sK110(X56,k2_zfmisc_1(sK2,sK3))),sK4)
        | k2_zfmisc_1(sK2,sK3) = k6_relat_1(X56)
        | ~ r2_hidden(sK109(X56,k2_zfmisc_1(sK2,sK3)),X56)
        | sK109(X56,k2_zfmisc_1(sK2,sK3)) != sK110(X56,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_45])])).

fof(f3921,plain,
    ( ! [X56] :
        ( ~ r2_hidden(k4_tarski(sK109(X56,k2_zfmisc_1(sK2,sK3)),sK110(X56,k2_zfmisc_1(sK2,sK3))),sK4)
        | sK109(X56,k2_zfmisc_1(sK2,sK3)) != sK110(X56,k2_zfmisc_1(sK2,sK3))
        | ~ r2_hidden(sK109(X56,k2_zfmisc_1(sK2,sK3)),X56)
        | k2_zfmisc_1(sK2,sK3) = k6_relat_1(X56)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2987])).

fof(f2987,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK109(X0,X1),sK110(X0,X1)),X1)
      | sK109(X0,X1) != sK110(X0,X1)
      | ~ r2_hidden(sK109(X0,X1),X0)
      | k6_relat_1(X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2390])).

fof(f2390,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK109(X0,X1) != sK110(X0,X1)
              | ~ r2_hidden(sK109(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK109(X0,X1),sK110(X0,X1)),X1) )
            & ( ( sK109(X0,X1) = sK110(X0,X1)
                & r2_hidden(sK109(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK109(X0,X1),sK110(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK109,sK110])],[f2388,f2389])).

fof(f2389,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK109(X0,X1) != sK110(X0,X1)
          | ~ r2_hidden(sK109(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK109(X0,X1),sK110(X0,X1)),X1) )
        & ( ( sK109(X0,X1) = sK110(X0,X1)
            & r2_hidden(sK109(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK109(X0,X1),sK110(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2388,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f2387])).

fof(f2387,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2386])).

fof(f2386,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1760])).

fof(f1760,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f3996,plain,
    ( ~ spl172_19
    | spl172_44
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3920,f3674,f3994,f3773])).

fof(f3994,plain,
    ( spl172_44
  <=> ! [X55] :
        ( ~ r2_hidden(k4_tarski(sK90(X55,k2_zfmisc_1(sK2,sK3)),sK91(X55,k2_zfmisc_1(sK2,sK3))),sK4)
        | ~ v1_relat_1(X55)
        | ~ r2_hidden(k4_tarski(sK90(X55,k2_zfmisc_1(sK2,sK3)),sK91(X55,k2_zfmisc_1(sK2,sK3))),X55)
        | k2_zfmisc_1(sK2,sK3) = X55 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_44])])).

fof(f3920,plain,
    ( ! [X55] :
        ( ~ r2_hidden(k4_tarski(sK90(X55,k2_zfmisc_1(sK2,sK3)),sK91(X55,k2_zfmisc_1(sK2,sK3))),sK4)
        | k2_zfmisc_1(sK2,sK3) = X55
        | ~ r2_hidden(k4_tarski(sK90(X55,k2_zfmisc_1(sK2,sK3)),sK91(X55,k2_zfmisc_1(sK2,sK3))),X55)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
        | ~ v1_relat_1(X55) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2870])).

fof(f2870,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2344])).

fof(f2344,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK90,sK91])],[f2342,f2343])).

fof(f2343,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK90(X0,X1),sK91(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2342,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2341])).

fof(f2341,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1664])).

fof(f1664,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f654])).

fof(f654,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f3992,plain,
    ( spl172_43
    | spl172_42
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3918,f3674,f3985,f3989])).

fof(f3989,plain,
    ( spl172_43
  <=> ! [X48,X47] : sK79(k2_zfmisc_1(sK2,sK3)) != k4_tarski(X47,X48) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_43])])).

fof(f3985,plain,
    ( spl172_42
  <=> ! [X44,X43,X45] :
        ( ~ r2_hidden(k4_tarski(sK77(X43,k2_zfmisc_1(sK2,sK3)),sK78(X43,k2_zfmisc_1(sK2,sK3))),sK4)
        | k4_tarski(X44,X45) != sK80(X43)
        | ~ r2_hidden(k4_tarski(sK77(X43,k2_zfmisc_1(sK2,sK3)),sK78(X43,k2_zfmisc_1(sK2,sK3))),X43)
        | k2_zfmisc_1(sK2,sK3) = X43 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_42])])).

fof(f3918,plain,
    ( ! [X52,X50,X53,X51,X49] :
        ( ~ r2_hidden(k4_tarski(sK77(X49,k2_zfmisc_1(sK2,sK3)),sK78(X49,k2_zfmisc_1(sK2,sK3))),sK4)
        | k2_zfmisc_1(sK2,sK3) = X49
        | ~ r2_hidden(k4_tarski(sK77(X49,k2_zfmisc_1(sK2,sK3)),sK78(X49,k2_zfmisc_1(sK2,sK3))),X49)
        | sK79(k2_zfmisc_1(sK2,sK3)) != k4_tarski(X50,X51)
        | k4_tarski(X52,X53) != sK80(X49) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2850])).

fof(f2850,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK79(X1)
      | k4_tarski(X8,X9) != sK80(X0) ) ),
    inference(cnf_transformation,[],[f2325])).

fof(f2325,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0) ) )
      | ( ! [X5,X6] : k4_tarski(X5,X6) != sK79(X1)
        & r2_hidden(sK79(X1),X1) )
      | ( ! [X8,X9] : k4_tarski(X8,X9) != sK80(X0)
        & r2_hidden(sK80(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK77,sK78,sK79,sK80])],[f2321,f2324,f2323,f2322])).

fof(f2322,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2323,plain,(
    ! [X1] :
      ( ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
     => ( ! [X6,X5] : k4_tarski(X5,X6) != sK79(X1)
        & r2_hidden(sK79(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f2324,plain,(
    ! [X0] :
      ( ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) )
     => ( ! [X9,X8] : k4_tarski(X8,X9) != sK80(X0)
        & r2_hidden(sK80(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2321,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(nnf_transformation,[],[f1658])).

fof(f1658,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(flattening,[],[f1657])).

fof(f1657,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(ennf_transformation,[],[f1509])).

fof(f1509,plain,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X4] :
            ~ ( ! [X5,X6] : k4_tarski(X5,X6) != X4
              & r2_hidden(X4,X1) )
        & ! [X7] :
            ~ ( ! [X8,X9] : k4_tarski(X8,X9) != X7
              & r2_hidden(X7,X0) ) )
     => X0 = X1 ) ),
    inference(rectify,[],[f299])).

fof(f299,axiom,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X0) ) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l131_zfmisc_1)).

fof(f3991,plain,
    ( spl172_43
    | spl172_41
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3917,f3674,f3981,f3989])).

fof(f3981,plain,
    ( spl172_41
  <=> ! [X42] :
        ( ~ r2_hidden(k4_tarski(sK77(X42,k2_zfmisc_1(sK2,sK3)),sK78(X42,k2_zfmisc_1(sK2,sK3))),sK4)
        | r2_hidden(sK80(X42),X42)
        | ~ r2_hidden(k4_tarski(sK77(X42,k2_zfmisc_1(sK2,sK3)),sK78(X42,k2_zfmisc_1(sK2,sK3))),X42)
        | k2_zfmisc_1(sK2,sK3) = X42 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_41])])).

fof(f3917,plain,
    ( ! [X47,X48,X46] :
        ( ~ r2_hidden(k4_tarski(sK77(X46,k2_zfmisc_1(sK2,sK3)),sK78(X46,k2_zfmisc_1(sK2,sK3))),sK4)
        | k2_zfmisc_1(sK2,sK3) = X46
        | ~ r2_hidden(k4_tarski(sK77(X46,k2_zfmisc_1(sK2,sK3)),sK78(X46,k2_zfmisc_1(sK2,sK3))),X46)
        | sK79(k2_zfmisc_1(sK2,sK3)) != k4_tarski(X47,X48)
        | r2_hidden(sK80(X46),X46) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2849])).

fof(f2849,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK79(X1)
      | r2_hidden(sK80(X0),X0) ) ),
    inference(cnf_transformation,[],[f2325])).

fof(f3987,plain,
    ( spl172_40
    | spl172_42
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3916,f3674,f3985,f3978])).

fof(f3978,plain,
    ( spl172_40
  <=> r2_hidden(sK79(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_40])])).

fof(f3916,plain,
    ( ! [X45,X43,X44] :
        ( ~ r2_hidden(k4_tarski(sK77(X43,k2_zfmisc_1(sK2,sK3)),sK78(X43,k2_zfmisc_1(sK2,sK3))),sK4)
        | k2_zfmisc_1(sK2,sK3) = X43
        | ~ r2_hidden(k4_tarski(sK77(X43,k2_zfmisc_1(sK2,sK3)),sK78(X43,k2_zfmisc_1(sK2,sK3))),X43)
        | r2_hidden(sK79(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
        | k4_tarski(X44,X45) != sK80(X43) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2848])).

fof(f2848,plain,(
    ! [X0,X8,X1,X9] :
      ( ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0)
      | r2_hidden(sK79(X1),X1)
      | k4_tarski(X8,X9) != sK80(X0) ) ),
    inference(cnf_transformation,[],[f2325])).

fof(f3983,plain,
    ( spl172_40
    | spl172_41
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3915,f3674,f3981,f3978])).

fof(f3915,plain,
    ( ! [X42] :
        ( ~ r2_hidden(k4_tarski(sK77(X42,k2_zfmisc_1(sK2,sK3)),sK78(X42,k2_zfmisc_1(sK2,sK3))),sK4)
        | k2_zfmisc_1(sK2,sK3) = X42
        | ~ r2_hidden(k4_tarski(sK77(X42,k2_zfmisc_1(sK2,sK3)),sK78(X42,k2_zfmisc_1(sK2,sK3))),X42)
        | r2_hidden(sK79(k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
        | r2_hidden(sK80(X42),X42) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2847])).

fof(f2847,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK77(X0,X1),sK78(X0,X1)),X0)
      | r2_hidden(sK79(X1),X1)
      | r2_hidden(sK80(X0),X0) ) ),
    inference(cnf_transformation,[],[f2325])).

fof(f3976,plain,
    ( spl172_38
    | spl172_39
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3914,f3674,f3974,f3971])).

fof(f3971,plain,
    ( spl172_38
  <=> ! [X38,X39] : ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X38,X39)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_38])])).

fof(f3974,plain,
    ( spl172_39
  <=> ! [X40,X41,X37] :
        ( ~ r2_hidden(k4_tarski(sK51(X37,k2_zfmisc_1(sK2,sK3)),sK52(X37,k2_zfmisc_1(sK2,sK3))),sK4)
        | ~ r1_tarski(X37,k2_zfmisc_1(X40,X41))
        | ~ r2_hidden(k4_tarski(sK51(X37,k2_zfmisc_1(sK2,sK3)),sK52(X37,k2_zfmisc_1(sK2,sK3))),X37)
        | k2_zfmisc_1(sK2,sK3) = X37 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_39])])).

fof(f3914,plain,
    ( ! [X39,X37,X41,X38,X40] :
        ( ~ r2_hidden(k4_tarski(sK51(X37,k2_zfmisc_1(sK2,sK3)),sK52(X37,k2_zfmisc_1(sK2,sK3))),sK4)
        | k2_zfmisc_1(sK2,sK3) = X37
        | ~ r2_hidden(k4_tarski(sK51(X37,k2_zfmisc_1(sK2,sK3)),sK52(X37,k2_zfmisc_1(sK2,sK3))),X37)
        | ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X38,X39))
        | ~ r1_tarski(X37,k2_zfmisc_1(X40,X41)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2786])).

fof(f2786,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X3)
      | X0 = X3
      | ~ r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f2276])).

fof(f2276,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ( ( ~ r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X0) )
        & ( r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X3)
          | r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X0) ) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK51,sK52])],[f2274,f2275])).

fof(f2275,plain,(
    ! [X3,X0] :
      ( ? [X6,X7] :
          ( ( ~ r2_hidden(k4_tarski(X6,X7),X3)
            | ~ r2_hidden(k4_tarski(X6,X7),X0) )
          & ( r2_hidden(k4_tarski(X6,X7),X3)
            | r2_hidden(k4_tarski(X6,X7),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X0) )
        & ( r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X3)
          | r2_hidden(k4_tarski(sK51(X0,X3),sK52(X0,X3)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2274,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( ( ~ r2_hidden(k4_tarski(X6,X7),X3)
            | ~ r2_hidden(k4_tarski(X6,X7),X0) )
          & ( r2_hidden(k4_tarski(X6,X7),X3)
            | r2_hidden(k4_tarski(X6,X7),X0) ) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(nnf_transformation,[],[f1640])).

fof(f1640,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( r2_hidden(k4_tarski(X6,X7),X0)
        <~> r2_hidden(k4_tarski(X6,X7),X3) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f1639])).

fof(f1639,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( r2_hidden(k4_tarski(X6,X7),X0)
        <~> r2_hidden(k4_tarski(X6,X7),X3) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f298])).

fof(f298,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ! [X6,X7] :
            ( r2_hidden(k4_tarski(X6,X7),X0)
          <=> r2_hidden(k4_tarski(X6,X7),X3) )
        & r1_tarski(X3,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
     => X0 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l130_zfmisc_1)).

fof(f3969,plain,
    ( ~ spl172_19
    | spl172_37
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3913,f3674,f3967,f3773])).

fof(f3967,plain,
    ( spl172_37
  <=> ! [X34,X36,X35] :
        ( ~ r2_hidden(k4_tarski(X34,sK162(k2_zfmisc_1(sK2,sK3),X35,X36)),sK4)
        | ~ r2_hidden(sK162(k2_zfmisc_1(sK2,sK3),X35,X36),X36)
        | k9_relat_1(k2_zfmisc_1(sK2,sK3),X35) = X36
        | ~ r2_hidden(X34,X35) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_37])])).

fof(f3913,plain,
    ( ! [X35,X36,X34] :
        ( ~ r2_hidden(k4_tarski(X34,sK162(k2_zfmisc_1(sK2,sK3),X35,X36)),sK4)
        | ~ r2_hidden(X34,X35)
        | k9_relat_1(k2_zfmisc_1(sK2,sK3),X35) = X36
        | ~ r2_hidden(sK162(k2_zfmisc_1(sK2,sK3),X35,X36),X36)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f3436])).

fof(f3436,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,sK162(X0,X1,X2)),X0)
      | ~ r2_hidden(X4,X1)
      | k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(sK162(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2525])).

fof(f2525,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK162(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK162(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK163(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK163(X0,X1,X2),sK162(X0,X1,X2)),X0) )
                | r2_hidden(sK162(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK164(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK164(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK162,sK163,sK164])],[f2521,f2524,f2523,f2522])).

fof(f2522,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK162(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK162(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK162(X0,X1,X2)),X0) )
          | r2_hidden(sK162(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2523,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK162(X0,X1,X2)),X0) )
     => ( r2_hidden(sK163(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK163(X0,X1,X2),sK162(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2524,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK164(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK164(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2521,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2520])).

fof(f2520,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2077])).

fof(f2077,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f647])).

fof(f647,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f3965,plain,
    ( ~ spl172_19
    | spl172_36
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3911,f3674,f3963,f3773])).

fof(f3963,plain,
    ( spl172_36
  <=> ! [X29,X31,X30] :
        ( ~ r2_hidden(k4_tarski(sK168(k2_zfmisc_1(sK2,sK3),X29,X30),X31),sK4)
        | ~ r2_hidden(sK168(k2_zfmisc_1(sK2,sK3),X29,X30),X30)
        | k10_relat_1(k2_zfmisc_1(sK2,sK3),X29) = X30
        | ~ r2_hidden(X31,X29) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_36])])).

fof(f3911,plain,
    ( ! [X30,X31,X29] :
        ( ~ r2_hidden(k4_tarski(sK168(k2_zfmisc_1(sK2,sK3),X29,X30),X31),sK4)
        | ~ r2_hidden(X31,X29)
        | k10_relat_1(k2_zfmisc_1(sK2,sK3),X29) = X30
        | ~ r2_hidden(sK168(k2_zfmisc_1(sK2,sK3),X29,X30),X30)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f3488])).

fof(f3488,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK168(X0,X1,X2),X4),X0)
      | ~ r2_hidden(X4,X1)
      | k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(sK168(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2544])).

fof(f2544,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK168(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK168(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK169(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK168(X0,X1,X2),sK169(X0,X1,X2)),X0) )
                | r2_hidden(sK168(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK170(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK170(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK168,sK169,sK170])],[f2540,f2543,f2542,f2541])).

fof(f2541,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK168(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK168(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK168(X0,X1,X2),X5),X0) )
          | r2_hidden(sK168(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2542,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK168(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK169(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK168(X0,X1,X2),sK169(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2543,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK170(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK170(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2540,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2539])).

fof(f2539,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2131])).

fof(f2131,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f648])).

fof(f648,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f3961,plain,
    ( ~ spl172_35
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3897,f3674,f3959])).

fof(f3959,plain,
    ( spl172_35
  <=> r2_hidden(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_35])])).

fof(f3897,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3698,f2627])).

fof(f2627,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f3887,plain,(
    spl172_30 ),
    inference(avatar_contradiction_clause,[],[f3876])).

fof(f3876,plain,
    ( $false
    | spl172_30 ),
    inference(resolution,[],[f3823,f3008])).

fof(f3008,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f1250])).

fof(f1250,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f3823,plain,
    ( ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | spl172_30 ),
    inference(avatar_component_clause,[],[f3822])).

fof(f3822,plain,
    ( spl172_30
  <=> m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_30])])).

fof(f3870,plain,(
    spl172_27 ),
    inference(avatar_contradiction_clause,[],[f3859])).

fof(f3859,plain,
    ( $false
    | spl172_27 ),
    inference(resolution,[],[f3811,f3008])).

fof(f3811,plain,
    ( ~ m1_subset_1(k6_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | spl172_27 ),
    inference(avatar_component_clause,[],[f3810])).

fof(f3810,plain,
    ( spl172_27
  <=> m1_subset_1(k6_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_27])])).

fof(f3858,plain,
    ( ~ spl172_34
    | ~ spl172_26 ),
    inference(avatar_split_clause,[],[f3852,f3800,f3856])).

fof(f3852,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)),sK4)
    | ~ spl172_26 ),
    inference(resolution,[],[f3801,f2755])).

fof(f2755,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1624])).

fof(f1624,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f3846,plain,(
    ~ spl172_25 ),
    inference(avatar_contradiction_clause,[],[f3845])).

fof(f3845,plain,
    ( $false
    | ~ spl172_25 ),
    inference(resolution,[],[f3798,f2955])).

fof(f2955,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f477])).

fof(f477,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f3798,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl172_25 ),
    inference(avatar_component_clause,[],[f3797])).

fof(f3844,plain,
    ( ~ spl172_33
    | ~ spl172_18 ),
    inference(avatar_split_clause,[],[f3833,f3767,f3842])).

fof(f3833,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK4)
    | ~ spl172_18 ),
    inference(resolution,[],[f3768,f3014])).

fof(f3014,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1778])).

fof(f1778,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f3840,plain,
    ( ~ spl172_31
    | spl172_32
    | ~ spl172_18 ),
    inference(avatar_split_clause,[],[f3831,f3767,f3838,f3835])).

fof(f3838,plain,
    ( spl172_32
  <=> sK4 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_32])])).

fof(f3831,plain,
    ( sK4 = k2_zfmisc_1(sK2,sK3)
    | ~ r1_tarski(k2_zfmisc_1(sK2,sK3),sK4)
    | ~ spl172_18 ),
    inference(resolution,[],[f3768,f3020])).

fof(f3020,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2398])).

fof(f2398,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2397])).

fof(f2397,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3827,plain,(
    spl172_19 ),
    inference(avatar_contradiction_clause,[],[f3825])).

fof(f3825,plain,
    ( $false
    | spl172_19 ),
    inference(resolution,[],[f3774,f2628])).

fof(f2628,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f3774,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | spl172_19 ),
    inference(avatar_component_clause,[],[f3773])).

fof(f3824,plain,
    ( ~ spl172_29
    | ~ spl172_30
    | spl172_2 ),
    inference(avatar_split_clause,[],[f3817,f3670,f3822,f3819])).

fof(f3670,plain,
    ( spl172_2
  <=> r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK2,sK2,sK3,k6_relat_1(sK2),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_2])])).

fof(f3817,plain,
    ( ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_relset_1(sK2,sK3,k5_relat_1(k6_relat_1(sK2),sK4),sK4)
    | spl172_2 ),
    inference(global_subsumption,[],[f2556,f3816])).

fof(f3816,plain,
    ( ~ r2_relset_1(sK2,sK3,k5_relat_1(k6_relat_1(sK2),sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | spl172_2 ),
    inference(superposition,[],[f3671,f2571])).

fof(f2571,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1528])).

fof(f1528,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1527])).

fof(f1527,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1230])).

fof(f1230,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f3671,plain,
    ( ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK2,sK2,sK3,k6_relat_1(sK2),sK4),sK4)
    | spl172_2 ),
    inference(avatar_component_clause,[],[f3670])).

fof(f2556,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f2165])).

fof(f2165,plain,
    ( ( ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK3,sK3,sK3,sK4,k6_partfun1(sK3)),sK4)
      | ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK2,sK2,sK3,k6_partfun1(sK2),sK4),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f1515,f2164])).

fof(f2164,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK3,sK3,sK3,sK4,k6_partfun1(sK3)),sK4)
        | ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK2,sK2,sK3,k6_partfun1(sK2),sK4),sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f1515,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1497])).

fof(f1497,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f1496])).

fof(f1496,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f3815,plain,
    ( ~ spl172_27
    | ~ spl172_28
    | spl172_1 ),
    inference(avatar_split_clause,[],[f3808,f3667,f3813,f3810])).

fof(f3667,plain,
    ( spl172_1
  <=> r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK3,sK3,sK3,sK4,k6_relat_1(sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_1])])).

fof(f3808,plain,
    ( ~ r2_relset_1(sK2,sK3,k5_relat_1(sK4,k6_relat_1(sK3)),sK4)
    | ~ m1_subset_1(k6_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | spl172_1 ),
    inference(global_subsumption,[],[f2556,f3807])).

fof(f3807,plain,
    ( ~ r2_relset_1(sK2,sK3,k5_relat_1(sK4,k6_relat_1(sK3)),sK4)
    | ~ m1_subset_1(k6_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl172_1 ),
    inference(superposition,[],[f3668,f2571])).

fof(f3668,plain,
    ( ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK3,sK3,sK3,sK4,k6_relat_1(sK3)),sK4)
    | spl172_1 ),
    inference(avatar_component_clause,[],[f3667])).

fof(f3806,plain,
    ( ~ spl172_12
    | spl172_4 ),
    inference(avatar_split_clause,[],[f3804,f3709,f3737])).

fof(f3737,plain,
    ( spl172_12
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_12])])).

fof(f3709,plain,
    ( spl172_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_4])])).

fof(f3804,plain,
    ( ~ v1_xboole_0(sK4)
    | spl172_4 ),
    inference(resolution,[],[f3710,f2950])).

fof(f3710,plain,
    ( ~ v1_funct_1(sK4)
    | spl172_4 ),
    inference(avatar_component_clause,[],[f3709])).

fof(f3803,plain,
    ( spl172_26
    | spl172_25
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3707,f3674,f3797,f3800])).

fof(f3707,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2926])).

fof(f2926,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1716])).

fof(f1716,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f1715])).

fof(f1715,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f3802,plain,
    ( spl172_25
    | spl172_26
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3705,f3674,f3800,f3797])).

fof(f3705,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2933])).

fof(f2933,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2366])).

fof(f3795,plain,
    ( ~ spl172_19
    | spl172_24
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3704,f3674,f3793,f3773])).

fof(f3704,plain,
    ( ! [X17] :
        ( v4_relat_1(sK4,X17)
        | ~ v4_relat_1(k2_zfmisc_1(sK2,sK3),X17)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f3226])).

fof(f3226,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | v4_relat_1(X2,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1925])).

fof(f1925,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1924])).

fof(f1924,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

fof(f3791,plain,
    ( ~ spl172_19
    | spl172_23
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3703,f3674,f3789,f3773])).

fof(f3703,plain,
    ( ! [X16] :
        ( v5_relat_1(sK4,X16)
        | ~ v5_relat_1(k2_zfmisc_1(sK2,sK3),X16)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f3196])).

fof(f3196,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | v5_relat_1(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f1911,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1910])).

fof(f1910,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

fof(f3787,plain,
    ( ~ spl172_22
    | spl172_12
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3702,f3674,f3737,f3784])).

fof(f3702,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3))
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2944])).

fof(f2944,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1728])).

fof(f1728,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f541])).

fof(f541,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f3786,plain,
    ( spl172_21
    | ~ spl172_22
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3701,f3674,f3784,f3781])).

fof(f3781,plain,
    ( spl172_21
  <=> ! [X15] : ~ r2_hidden(X15,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_21])])).

fof(f3701,plain,
    ( ! [X15] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3))
        | ~ r2_hidden(X15,sK4) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2922])).

fof(f2922,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1710])).

fof(f1710,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f629])).

fof(f629,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f3779,plain,
    ( ~ spl172_19
    | ~ spl172_20
    | spl172_4
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3700,f3674,f3709,f3776,f3773])).

fof(f3700,plain,
    ( v1_funct_1(sK4)
    | ~ v1_funct_1(k2_zfmisc_1(sK2,sK3))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2784])).

fof(f2784,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1638])).

fof(f1638,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1637])).

fof(f1637,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f892])).

fof(f892,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f3771,plain,
    ( spl172_7
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3770,f3674,f3719])).

fof(f3770,plain,
    ( v1_relat_1(sK4)
    | ~ spl172_3 ),
    inference(global_subsumption,[],[f3682])).

fof(f3682,plain,
    ( v1_relat_1(sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2616])).

fof(f2616,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1559])).

fof(f1559,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3769,plain,
    ( spl172_18
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3697,f3674,f3767])).

fof(f3697,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2585])).

fof(f2585,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2181,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3765,plain,
    ( spl172_17
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3695,f3674,f3762])).

fof(f3695,plain,
    ( r2_relset_1(sK2,sK3,sK4,sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f3656])).

fof(f3656,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f2561])).

fof(f2561,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1521])).

fof(f1521,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1520])).

fof(f1520,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1238])).

fof(f1238,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f3764,plain,
    ( spl172_17
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3694,f3674,f3762])).

fof(f3694,plain,
    ( r2_relset_1(sK2,sK3,sK4,sK4)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f3655])).

fof(f3655,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f3546])).

fof(f3546,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f2559])).

fof(f2559,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2166])).

fof(f3760,plain,
    ( spl172_16
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3693,f3674,f3758])).

fof(f3693,plain,
    ( v5_relat_1(sK4,sK3)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f3208])).

fof(f3208,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f1923])).

fof(f1923,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f3756,plain,
    ( spl172_15
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3692,f3674,f3754])).

fof(f3692,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f3207])).

fof(f3207,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f1923])).

fof(f3752,plain,
    ( ~ spl172_13
    | spl172_14
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3691,f3674,f3746,f3741])).

fof(f3746,plain,
    ( spl172_14
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_14])])).

fof(f3691,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ v1_xboole_0(sK2)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2961])).

fof(f2961,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1741])).

fof(f1741,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1469])).

fof(f1469,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f3750,plain,
    ( spl172_13
    | ~ spl172_11
    | ~ spl172_14
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3690,f3674,f3746,f3734,f3741])).

fof(f3690,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2960])).

fof(f2960,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1740])).

fof(f1740,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1739])).

fof(f1739,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1470])).

fof(f1470,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f3748,plain,
    ( spl172_5
    | ~ spl172_4
    | ~ spl172_14
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3689,f3674,f3746,f3709,f3712])).

fof(f3712,plain,
    ( spl172_5
  <=> v1_funct_2(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_5])])).

fof(f3689,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(sK4,sK2,sK3)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2959])).

fof(f2959,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f1738])).

fof(f1738,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1737])).

fof(f1737,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1468])).

fof(f1468,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f3743,plain,
    ( ~ spl172_13
    | spl172_12
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3688,f3674,f3737,f3741])).

fof(f3688,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2928])).

fof(f2928,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1718])).

fof(f1718,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1212])).

fof(f1212,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f3739,plain,
    ( ~ spl172_11
    | spl172_12
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3687,f3674,f3737,f3734])).

fof(f3687,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK3)
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2927])).

fof(f2927,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1717])).

fof(f1717,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1213])).

fof(f1213,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f3732,plain,
    ( ~ spl172_4
    | ~ spl172_5
    | spl172_10
    | spl172_9
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3684,f3674,f3726,f3730,f3712,f3709])).

fof(f3730,plain,
    ( spl172_10
  <=> ! [X10] :
        ( ~ r1_tarski(sK3,X10)
        | v1_funct_2(sK4,sK2,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_10])])).

fof(f3726,plain,
    ( spl172_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_9])])).

fof(f3684,plain,
    ( ! [X10] :
        ( k1_xboole_0 = sK3
        | ~ r1_tarski(sK3,X10)
        | v1_funct_2(sK4,sK2,X10)
        | ~ v1_funct_2(sK4,sK2,sK3)
        | ~ v1_funct_1(sK4) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2760])).

fof(f2760,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1630])).

fof(f1630,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f1629])).

fof(f1629,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1504])).

fof(f1504,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f3728,plain,
    ( ~ spl172_4
    | ~ spl172_5
    | spl172_8
    | spl172_9
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3683,f3674,f3726,f3723,f3712,f3709])).

fof(f3723,plain,
    ( spl172_8
  <=> ! [X9] :
        ( ~ r2_hidden(X9,sK2)
        | r2_hidden(k1_funct_1(sK4,X9),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_8])])).

fof(f3683,plain,
    ( ! [X9] :
        ( k1_xboole_0 = sK3
        | ~ r2_hidden(X9,sK2)
        | r2_hidden(k1_funct_1(sK4,X9),sK3)
        | ~ v1_funct_2(sK4,sK2,sK3)
        | ~ v1_funct_1(sK4) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2757])).

fof(f2757,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1628])).

fof(f1628,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f1627])).

fof(f1627,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1502])).

fof(f1502,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f3721,plain,
    ( spl172_7
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3682,f3674,f3719])).

fof(f3717,plain,
    ( ~ spl172_4
    | ~ spl172_5
    | spl172_6
    | ~ spl172_3 ),
    inference(avatar_split_clause,[],[f3679,f3674,f3715,f3712,f3709])).

fof(f3715,plain,
    ( spl172_6
  <=> ! [X2] :
        ( r2_hidden(sK5(sK2,X2,sK4),sK2)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | r2_relset_1(sK2,sK3,X2,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_6])])).

fof(f3679,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(sK2,X2,sK4),sK2)
        | r2_relset_1(sK2,sK3,X2,sK4)
        | ~ v1_funct_2(sK4,sK2,sK3)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(X2,sK2,sK3)
        | ~ v1_funct_1(X2) )
    | ~ spl172_3 ),
    inference(resolution,[],[f3675,f2562])).

fof(f2562,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK5(X0,X2,X3),X0)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2168])).

fof(f2168,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
            & r2_hidden(sK5(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1523,f2167])).

fof(f2167,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
        & r2_hidden(sK5(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1523,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1522])).

fof(f1522,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1491])).

fof(f1491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f3676,plain,(
    spl172_3 ),
    inference(avatar_split_clause,[],[f2556,f3674])).

fof(f3672,plain,
    ( ~ spl172_1
    | ~ spl172_2 ),
    inference(avatar_split_clause,[],[f3665,f3670,f3667])).

fof(f3665,plain,
    ( ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK2,sK2,sK3,k6_relat_1(sK2),sK4),sK4)
    | ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK3,sK3,sK3,sK4,k6_relat_1(sK3)),sK4) ),
    inference(forward_demodulation,[],[f3664,f2581])).

fof(f2581,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f1486])).

fof(f1486,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f3664,plain,
    ( ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK3,sK3,sK3,sK4,k6_relat_1(sK3)),sK4)
    | ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK2,sK2,sK3,k6_partfun1(sK2),sK4),sK4) ),
    inference(forward_demodulation,[],[f2557,f2581])).

fof(f2557,plain,
    ( ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK3,sK3,sK3,sK4,k6_partfun1(sK3)),sK4)
    | ~ r2_relset_1(sK2,sK3,k4_relset_1(sK2,sK2,sK2,sK3,k6_partfun1(sK2),sK4),sK4) ),
    inference(cnf_transformation,[],[f2165])).
%------------------------------------------------------------------------------
