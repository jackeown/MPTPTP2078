%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t72_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:31 EDT 2019

% Result     : Theorem 2.79s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  863 (2598 expanded)
%              Number of leaves         :  235 (1162 expanded)
%              Depth                    :   12
%              Number of atoms          : 2692 (7295 expanded)
%              Number of equality atoms :  222 ( 785 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f109,f116,f148,f156,f163,f171,f272,f277,f282,f287,f314,f323,f331,f366,f370,f374,f378,f382,f409,f417,f424,f629,f634,f660,f668,f675,f683,f714,f723,f731,f855,f856,f872,f876,f880,f884,f888,f923,f931,f938,f1042,f1047,f1052,f1057,f1084,f1093,f1101,f1142,f1146,f1150,f1154,f1166,f1193,f1201,f1208,f1295,f1296,f1297,f1298,f1404,f1412,f1431,f1487,f1501,f1515,f1543,f1557,f1563,f1641,f1655,f1687,f1701,f1832,f1834,f1842,f1851,f2796,f2809,f2822,f2835,f2839,f2843,f2847,f2851,f2855,f2891,f2899,f2906,f3063,f3064,f3077,f3082,f3108,f3116,f3123,f3131,f3162,f3171,f3179,f3249,f3262,f3275,f3288,f3292,f3296,f3300,f3304,f3308,f3344,f3352,f3359,f3391,f3399,f3409,f3419,f3444,f3450,f3460,f3570,f3571,f3584,f3589,f3615,f3623,f3630,f3638,f3669,f3678,f3686,f3712,f3717,f3722,f3727,f3754,f3763,f3771,f3845,f3858,f3871,f3884,f3888,f3892,f3896,f3900,f3904,f3918,f3919,f3932,f3965,f3973,f3980,f3990,f4016,f4024,f4031,f4039,f4070,f4079,f4087,f4174,f4230,f4235,f4240,f4245,f4272,f4281,f4289,f4365,f4378,f4391,f4404,f4408,f4412,f4416,f4420,f4424,f4455,f4456,f4464,f4477,f4478,f4479,f4508,f4516,f4523,f4536])).

fof(f4536,plain,
    ( ~ spl4_4
    | ~ spl4_28
    | ~ spl4_64
    | ~ spl4_132
    | spl4_389 ),
    inference(avatar_contradiction_clause,[],[f4535])).

fof(f4535,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_64
    | ~ spl4_132
    | ~ spl4_389 ),
    inference(subsumption_resolution,[],[f4534,f115])).

fof(f115,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f4534,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_64
    | ~ spl4_132
    | ~ spl4_389 ),
    inference(subsumption_resolution,[],[f4533,f865])).

fof(f865,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl4_64
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f4533,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_132
    | ~ spl4_389 ),
    inference(subsumption_resolution,[],[f4532,f359])).

fof(f359,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl4_28
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f4532,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_132
    | ~ spl4_389 ),
    inference(subsumption_resolution,[],[f4529,f1536])).

fof(f1536,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_132 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f1535,plain,
    ( spl4_132
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f4529,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_389 ),
    inference(resolution,[],[f4463,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',t49_pre_topc)).

fof(f4463,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_389 ),
    inference(avatar_component_clause,[],[f4462])).

fof(f4462,plain,
    ( spl4_389
  <=> ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_389])])).

fof(f4523,plain,
    ( spl4_398
    | ~ spl4_362 ),
    inference(avatar_split_clause,[],[f4489,f4354,f4521])).

fof(f4521,plain,
    ( spl4_398
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_398])])).

fof(f4354,plain,
    ( spl4_362
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_362])])).

fof(f4489,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_362 ),
    inference(resolution,[],[f4355,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',t3_subset)).

fof(f4355,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_362 ),
    inference(avatar_component_clause,[],[f4354])).

fof(f4516,plain,
    ( spl4_396
    | ~ spl4_4
    | ~ spl4_362 ),
    inference(avatar_split_clause,[],[f4509,f4354,f114,f4514])).

fof(f4514,plain,
    ( spl4_396
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_396])])).

fof(f4509,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_362 ),
    inference(subsumption_resolution,[],[f4487,f115])).

fof(f4487,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_362 ),
    inference(resolution,[],[f4355,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',projectivity_k2_pre_topc)).

fof(f4508,plain,
    ( spl4_394
    | ~ spl4_4
    | ~ spl4_272
    | ~ spl4_362 ),
    inference(avatar_split_clause,[],[f4501,f4354,f3636,f114,f4506])).

fof(f4506,plain,
    ( spl4_394
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_394])])).

fof(f3636,plain,
    ( spl4_272
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_272])])).

fof(f4501,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_272
    | ~ spl4_362 ),
    inference(forward_demodulation,[],[f4500,f3637])).

fof(f3637,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_272 ),
    inference(avatar_component_clause,[],[f3636])).

fof(f4500,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_362 ),
    inference(subsumption_resolution,[],[f4486,f115])).

fof(f4486,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_362 ),
    inference(resolution,[],[f4355,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',d2_tops_1)).

fof(f4479,plain,
    ( spl4_386
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f4446,f3061,f4453])).

fof(f4453,plain,
    ( spl4_386
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_386])])).

fof(f3061,plain,
    ( spl4_194
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f4446,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_194 ),
    inference(superposition,[],[f87,f3062])).

fof(f3062,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_194 ),
    inference(avatar_component_clause,[],[f3061])).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',commutativity_k3_xboole_0)).

fof(f4478,plain,
    ( spl4_386
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f4445,f3061,f4453])).

fof(f4445,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_194 ),
    inference(superposition,[],[f87,f3062])).

fof(f4477,plain,
    ( ~ spl4_391
    | spl4_392
    | ~ spl4_62
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f4440,f3061,f853,f4475,f4469])).

fof(f4469,plain,
    ( spl4_391
  <=> ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_391])])).

fof(f4475,plain,
    ( spl4_392
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_392])])).

fof(f853,plain,
    ( spl4_62
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f4440,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_62
    | ~ spl4_194 ),
    inference(superposition,[],[f1288,f3062])).

fof(f1288,plain,
    ( ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,sK1),k3_xboole_0(X1,k2_pre_topc(sK0,sK1)))
        | ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X1) )
    | ~ spl4_62 ),
    inference(superposition,[],[f75,f854])).

fof(f854,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f853])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',t26_xboole_1)).

fof(f4464,plain,
    ( ~ spl4_389
    | spl4_1
    | ~ spl4_62
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f4457,f3061,f853,f100,f4462])).

fof(f100,plain,
    ( spl4_1
  <=> ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4457,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_1
    | ~ spl4_62
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f4439,f101])).

fof(f101,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f4439,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_62
    | ~ spl4_194 ),
    inference(superposition,[],[f1287,f3062])).

fof(f1287,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(X0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) )
    | ~ spl4_62 ),
    inference(superposition,[],[f75,f854])).

fof(f4456,plain,
    ( spl4_386
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f4432,f3061,f4453])).

fof(f4432,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_194 ),
    inference(superposition,[],[f3062,f87])).

fof(f4455,plain,
    ( spl4_386
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f4431,f3061,f4453])).

fof(f4431,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_194 ),
    inference(superposition,[],[f3062,f87])).

fof(f4424,plain,
    ( ~ spl4_264
    | spl4_363 ),
    inference(avatar_contradiction_clause,[],[f4423])).

fof(f4423,plain,
    ( $false
    | ~ spl4_264
    | ~ spl4_363 ),
    inference(subsumption_resolution,[],[f4421,f3583])).

fof(f3583,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_264 ),
    inference(avatar_component_clause,[],[f3582])).

fof(f3582,plain,
    ( spl4_264
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_264])])).

fof(f4421,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_363 ),
    inference(resolution,[],[f4358,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',dt_k3_subset_1)).

fof(f4358,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_363 ),
    inference(avatar_component_clause,[],[f4357])).

fof(f4357,plain,
    ( spl4_363
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_363])])).

fof(f4420,plain,
    ( ~ spl4_363
    | spl4_384
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4346,f3636,f4418,f4357])).

fof(f4418,plain,
    ( spl4_384
  <=> ! [X3] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_384])])).

fof(f4346,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_272 ),
    inference(superposition,[],[f93,f3637])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',t31_subset_1)).

fof(f4416,plain,
    ( ~ spl4_363
    | spl4_382
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4345,f3636,f4414,f4357])).

fof(f4414,plain,
    ( spl4_382
  <=> ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_382])])).

fof(f4345,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_272 ),
    inference(superposition,[],[f93,f3637])).

fof(f4412,plain,
    ( ~ spl4_363
    | spl4_380
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4344,f3636,f4410,f4357])).

fof(f4410,plain,
    ( spl4_380
  <=> ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_380])])).

fof(f4344,plain,
    ( ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_272 ),
    inference(superposition,[],[f92,f3637])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f4408,plain,
    ( ~ spl4_363
    | spl4_378
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4343,f3636,f4406,f4357])).

fof(f4406,plain,
    ( spl4_378
  <=> ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_378])])).

fof(f4343,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_272 ),
    inference(superposition,[],[f92,f3637])).

fof(f4404,plain,
    ( spl4_374
    | ~ spl4_363
    | ~ spl4_377
    | ~ spl4_34
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4340,f3636,f372,f4402,f4357,f4396])).

fof(f4396,plain,
    ( spl4_374
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_374])])).

fof(f4402,plain,
    ( spl4_377
  <=> ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_377])])).

fof(f372,plain,
    ( spl4_34
  <=> ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f4340,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_34
    | ~ spl4_272 ),
    inference(superposition,[],[f373,f3637])).

fof(f373,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X2) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f372])).

fof(f4391,plain,
    ( spl4_370
    | ~ spl4_363
    | ~ spl4_373
    | ~ spl4_36
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4339,f3636,f376,f4389,f4357,f4383])).

fof(f4383,plain,
    ( spl4_370
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_370])])).

fof(f4389,plain,
    ( spl4_373
  <=> ~ r1_tarski(sK1,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_373])])).

fof(f376,plain,
    ( spl4_36
  <=> ! [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f4339,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_36
    | ~ spl4_272 ),
    inference(superposition,[],[f377,f3637])).

fof(f377,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f376])).

fof(f4378,plain,
    ( ~ spl4_367
    | ~ spl4_363
    | spl4_368
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4336,f3636,f372,f364,f107,f4376,f4357,f4370])).

fof(f4370,plain,
    ( spl4_367
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_367])])).

fof(f4376,plain,
    ( spl4_368
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_368])])).

fof(f107,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f364,plain,
    ( spl4_30
  <=> ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f4336,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),sK1)
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_272 ),
    inference(superposition,[],[f1587,f3637])).

fof(f1587,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1570,f95])).

fof(f1570,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34 ),
    inference(resolution,[],[f1391,f373])).

fof(f1391,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)),sK1)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1390,f95])).

fof(f1390,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)),sK1)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f1385,f108])).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f1385,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)),sK1)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_30 ),
    inference(resolution,[],[f365,f92])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),sK1) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f364])).

fof(f4365,plain,
    ( ~ spl4_361
    | ~ spl4_363
    | spl4_364
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f4335,f3636,f376,f368,f107,f4363,f4357,f4351])).

fof(f4351,plain,
    ( spl4_361
  <=> ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_361])])).

fof(f4363,plain,
    ( spl4_364
  <=> r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_364])])).

fof(f368,plain,
    ( spl4_32
  <=> ! [X1] :
        ( r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f4335,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_272 ),
    inference(superposition,[],[f1613,f3637])).

fof(f1613,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0) )
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f1596,f95])).

fof(f1596,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36 ),
    inference(resolution,[],[f1465,f377])).

fof(f1465,plain,
    ( ! [X3] :
        ( r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3)))
        | ~ r1_tarski(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1464,f95])).

fof(f1464,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3)))
        | ~ r1_tarski(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1463,f108])).

fof(f1463,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X3)))
        | ~ r1_tarski(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_32 ),
    inference(resolution,[],[f369,f92])).

fof(f369,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X1)) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f368])).

fof(f4289,plain,
    ( spl4_358
    | ~ spl4_346 ),
    inference(avatar_split_clause,[],[f4262,f4219,f4287])).

fof(f4287,plain,
    ( spl4_358
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_358])])).

fof(f4219,plain,
    ( spl4_346
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_346])])).

fof(f4262,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))))
    | ~ spl4_346 ),
    inference(resolution,[],[f4220,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',involutiveness_k3_subset_1)).

fof(f4220,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_346 ),
    inference(avatar_component_clause,[],[f4219])).

fof(f4281,plain,
    ( spl4_356
    | ~ spl4_346 ),
    inference(avatar_split_clause,[],[f4253,f4219,f4279])).

fof(f4279,plain,
    ( spl4_356
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_356])])).

fof(f4253,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_346 ),
    inference(resolution,[],[f4220,f76])).

fof(f4272,plain,
    ( spl4_354
    | ~ spl4_4
    | ~ spl4_268
    | ~ spl4_346 ),
    inference(avatar_split_clause,[],[f4265,f4219,f3621,f114,f4270])).

fof(f4270,plain,
    ( spl4_354
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_354])])).

fof(f3621,plain,
    ( spl4_268
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_268])])).

fof(f4265,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_268
    | ~ spl4_346 ),
    inference(forward_demodulation,[],[f4264,f3622])).

fof(f3622,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_268 ),
    inference(avatar_component_clause,[],[f3621])).

fof(f4264,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_346 ),
    inference(subsumption_resolution,[],[f4250,f115])).

fof(f4250,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_346 ),
    inference(resolution,[],[f4220,f81])).

fof(f4245,plain,
    ( ~ spl4_4
    | ~ spl4_264
    | spl4_347 ),
    inference(avatar_contradiction_clause,[],[f4244])).

fof(f4244,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_264
    | ~ spl4_347 ),
    inference(subsumption_resolution,[],[f4243,f115])).

fof(f4243,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_264
    | ~ spl4_347 ),
    inference(subsumption_resolution,[],[f4241,f3583])).

fof(f4241,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_347 ),
    inference(resolution,[],[f4223,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',dt_k2_pre_topc)).

fof(f4223,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_347 ),
    inference(avatar_component_clause,[],[f4222])).

fof(f4222,plain,
    ( spl4_347
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_347])])).

fof(f4240,plain,
    ( ~ spl4_347
    | spl4_352
    | ~ spl4_4
    | ~ spl4_268 ),
    inference(avatar_split_clause,[],[f4236,f3621,f114,f4238,f4222])).

fof(f4238,plain,
    ( spl4_352
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_352])])).

fof(f4236,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_268 ),
    inference(subsumption_resolution,[],[f4216,f115])).

fof(f4216,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_268 ),
    inference(superposition,[],[f78,f3622])).

fof(f4235,plain,
    ( ~ spl4_347
    | spl4_350
    | ~ spl4_4
    | ~ spl4_268 ),
    inference(avatar_split_clause,[],[f4231,f3621,f114,f4233,f4222])).

fof(f4233,plain,
    ( spl4_350
  <=> ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_350])])).

fof(f4231,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_268 ),
    inference(subsumption_resolution,[],[f4215,f115])).

fof(f4215,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_268 ),
    inference(superposition,[],[f78,f3622])).

fof(f4230,plain,
    ( ~ spl4_347
    | spl4_348
    | ~ spl4_4
    | ~ spl4_268 ),
    inference(avatar_split_clause,[],[f4217,f3621,f114,f4228,f4222])).

fof(f4228,plain,
    ( spl4_348
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_348])])).

fof(f4217,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_268 ),
    inference(subsumption_resolution,[],[f4214,f115])).

fof(f4214,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_268 ),
    inference(superposition,[],[f79,f3622])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',t48_pre_topc)).

fof(f4174,plain,
    ( ~ spl4_4
    | ~ spl4_28
    | ~ spl4_30
    | ~ spl4_44
    | spl4_169 ),
    inference(avatar_contradiction_clause,[],[f4173])).

fof(f4173,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_30
    | ~ spl4_44
    | ~ spl4_169 ),
    inference(subsumption_resolution,[],[f4172,f115])).

fof(f4172,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_30
    | ~ spl4_44
    | ~ spl4_169 ),
    inference(subsumption_resolution,[],[f4171,f359])).

fof(f4171,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_30
    | ~ spl4_44
    | ~ spl4_169 ),
    inference(subsumption_resolution,[],[f4164,f619])).

fof(f619,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl4_44
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f4164,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_30
    | ~ spl4_169 ),
    inference(resolution,[],[f1389,f2802])).

fof(f2802,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ spl4_169 ),
    inference(avatar_component_clause,[],[f2801])).

fof(f2801,plain,
    ( spl4_169
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_169])])).

fof(f1389,plain,
    ( ! [X4] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(X4,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
        | ~ m1_subset_1(k2_pre_topc(X4,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
    | ~ spl4_30 ),
    inference(resolution,[],[f365,f79])).

fof(f4087,plain,
    ( spl4_344
    | ~ spl4_322 ),
    inference(avatar_split_clause,[],[f4060,f3921,f4085])).

fof(f4085,plain,
    ( spl4_344
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_344])])).

fof(f3921,plain,
    ( spl4_322
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_322])])).

fof(f4060,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))))
    | ~ spl4_322 ),
    inference(resolution,[],[f3922,f94])).

fof(f3922,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_322 ),
    inference(avatar_component_clause,[],[f3921])).

fof(f4079,plain,
    ( spl4_342
    | ~ spl4_322 ),
    inference(avatar_split_clause,[],[f4051,f3921,f4077])).

fof(f4077,plain,
    ( spl4_342
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_342])])).

fof(f4051,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),u1_struct_0(sK0))
    | ~ spl4_322 ),
    inference(resolution,[],[f3922,f76])).

fof(f4070,plain,
    ( spl4_340
    | ~ spl4_4
    | ~ spl4_190
    | ~ spl4_322 ),
    inference(avatar_split_clause,[],[f4063,f3921,f2897,f114,f4068])).

fof(f4068,plain,
    ( spl4_340
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_340])])).

fof(f2897,plain,
    ( spl4_190
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_190])])).

fof(f4063,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))))
    | ~ spl4_4
    | ~ spl4_190
    | ~ spl4_322 ),
    inference(forward_demodulation,[],[f4062,f2898])).

fof(f2898,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl4_190 ),
    inference(avatar_component_clause,[],[f2897])).

fof(f4062,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))))
    | ~ spl4_4
    | ~ spl4_322 ),
    inference(subsumption_resolution,[],[f4048,f115])).

fof(f4048,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_322 ),
    inference(resolution,[],[f3922,f81])).

fof(f4039,plain,
    ( spl4_338
    | ~ spl4_324 ),
    inference(avatar_split_clause,[],[f4007,f3930,f4037])).

fof(f4037,plain,
    ( spl4_338
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_338])])).

fof(f3930,plain,
    ( spl4_324
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_324])])).

fof(f4007,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl4_324 ),
    inference(resolution,[],[f3931,f94])).

fof(f3931,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_324 ),
    inference(avatar_component_clause,[],[f3930])).

fof(f4031,plain,
    ( spl4_336
    | ~ spl4_324 ),
    inference(avatar_split_clause,[],[f3998,f3930,f4029])).

fof(f4029,plain,
    ( spl4_336
  <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_336])])).

fof(f3998,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),u1_struct_0(sK0))
    | ~ spl4_324 ),
    inference(resolution,[],[f3931,f76])).

fof(f4024,plain,
    ( spl4_334
    | ~ spl4_4
    | ~ spl4_324 ),
    inference(avatar_split_clause,[],[f4017,f3930,f114,f4022])).

fof(f4022,plain,
    ( spl4_334
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_334])])).

fof(f4017,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl4_4
    | ~ spl4_324 ),
    inference(subsumption_resolution,[],[f3996,f115])).

fof(f3996,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_324 ),
    inference(resolution,[],[f3931,f82])).

fof(f4016,plain,
    ( spl4_332
    | ~ spl4_4
    | ~ spl4_324 ),
    inference(avatar_split_clause,[],[f4009,f3930,f114,f4014])).

fof(f4014,plain,
    ( spl4_332
  <=> k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_332])])).

fof(f4009,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))))
    | ~ spl4_4
    | ~ spl4_324 ),
    inference(subsumption_resolution,[],[f3995,f115])).

fof(f3995,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_324 ),
    inference(resolution,[],[f3931,f81])).

fof(f3990,plain,
    ( ~ spl4_4
    | ~ spl4_164
    | spl4_323 ),
    inference(avatar_contradiction_clause,[],[f3989])).

fof(f3989,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_164
    | ~ spl4_323 ),
    inference(subsumption_resolution,[],[f3988,f115])).

fof(f3988,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_164
    | ~ spl4_323 ),
    inference(subsumption_resolution,[],[f3986,f2786])).

fof(f2786,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_164 ),
    inference(avatar_component_clause,[],[f2785])).

fof(f2785,plain,
    ( spl4_164
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f3986,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_323 ),
    inference(resolution,[],[f3925,f83])).

fof(f3925,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_323 ),
    inference(avatar_component_clause,[],[f3924])).

fof(f3924,plain,
    ( spl4_323
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_323])])).

fof(f3980,plain,
    ( spl4_330
    | ~ spl4_296 ),
    inference(avatar_split_clause,[],[f3946,f3834,f3978])).

fof(f3978,plain,
    ( spl4_330
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_330])])).

fof(f3834,plain,
    ( spl4_296
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_296])])).

fof(f3946,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_296 ),
    inference(resolution,[],[f3835,f76])).

fof(f3835,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_296 ),
    inference(avatar_component_clause,[],[f3834])).

fof(f3973,plain,
    ( spl4_328
    | ~ spl4_4
    | ~ spl4_296 ),
    inference(avatar_split_clause,[],[f3966,f3834,f114,f3971])).

fof(f3971,plain,
    ( spl4_328
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_328])])).

fof(f3966,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_296 ),
    inference(subsumption_resolution,[],[f3944,f115])).

fof(f3944,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_296 ),
    inference(resolution,[],[f3835,f82])).

fof(f3965,plain,
    ( spl4_326
    | ~ spl4_4
    | ~ spl4_206
    | ~ spl4_296 ),
    inference(avatar_split_clause,[],[f3958,f3834,f3129,f114,f3963])).

fof(f3963,plain,
    ( spl4_326
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_326])])).

fof(f3129,plain,
    ( spl4_206
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f3958,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_206
    | ~ spl4_296 ),
    inference(forward_demodulation,[],[f3957,f3130])).

fof(f3130,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_206 ),
    inference(avatar_component_clause,[],[f3129])).

fof(f3957,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_296 ),
    inference(subsumption_resolution,[],[f3943,f115])).

fof(f3943,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_296 ),
    inference(resolution,[],[f3835,f81])).

fof(f3932,plain,
    ( ~ spl4_323
    | spl4_324
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f3910,f712,f3930,f3924])).

fof(f712,plain,
    ( spl4_56
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f3910,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_56 ),
    inference(superposition,[],[f90,f713])).

fof(f713,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f712])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',dt_k9_subset_1)).

fof(f3919,plain,
    ( spl4_320
    | ~ spl4_44
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f3909,f712,f618,f3916])).

fof(f3916,plain,
    ( spl4_320
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_320])])).

fof(f3909,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_44
    | ~ spl4_56 ),
    inference(superposition,[],[f724,f713])).

fof(f724,plain,
    ( ! [X3] : k3_xboole_0(X3,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X3)
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f697,f696])).

fof(f696,plain,
    ( ! [X2] : k3_xboole_0(X2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_44 ),
    inference(resolution,[],[f619,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',redefinition_k9_subset_1)).

fof(f697,plain,
    ( ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X3)
    | ~ spl4_44 ),
    inference(resolution,[],[f619,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',commutativity_k9_subset_1)).

fof(f3918,plain,
    ( spl4_320
    | ~ spl4_44
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f3907,f712,f618,f3916])).

fof(f3907,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_44
    | ~ spl4_56 ),
    inference(superposition,[],[f713,f724])).

fof(f3904,plain,
    ( ~ spl4_198
    | spl4_297 ),
    inference(avatar_contradiction_clause,[],[f3903])).

fof(f3903,plain,
    ( $false
    | ~ spl4_198
    | ~ spl4_297 ),
    inference(subsumption_resolution,[],[f3901,f3076])).

fof(f3076,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_198 ),
    inference(avatar_component_clause,[],[f3075])).

fof(f3075,plain,
    ( spl4_198
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f3901,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_297 ),
    inference(resolution,[],[f3838,f95])).

fof(f3838,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_297 ),
    inference(avatar_component_clause,[],[f3837])).

fof(f3837,plain,
    ( spl4_297
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_297])])).

fof(f3900,plain,
    ( ~ spl4_297
    | spl4_318
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3826,f3129,f3898,f3837])).

fof(f3898,plain,
    ( spl4_318
  <=> ! [X3] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_318])])).

fof(f3826,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_206 ),
    inference(superposition,[],[f93,f3130])).

fof(f3896,plain,
    ( ~ spl4_297
    | spl4_316
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3825,f3129,f3894,f3837])).

fof(f3894,plain,
    ( spl4_316
  <=> ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_316])])).

fof(f3825,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_206 ),
    inference(superposition,[],[f93,f3130])).

fof(f3892,plain,
    ( ~ spl4_297
    | spl4_314
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3824,f3129,f3890,f3837])).

fof(f3890,plain,
    ( spl4_314
  <=> ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_314])])).

fof(f3824,plain,
    ( ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_206 ),
    inference(superposition,[],[f92,f3130])).

fof(f3888,plain,
    ( ~ spl4_297
    | spl4_312
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3823,f3129,f3886,f3837])).

fof(f3886,plain,
    ( spl4_312
  <=> ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_312])])).

fof(f3823,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_206 ),
    inference(superposition,[],[f92,f3130])).

fof(f3884,plain,
    ( spl4_308
    | ~ spl4_297
    | ~ spl4_311
    | ~ spl4_34
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3820,f3129,f372,f3882,f3837,f3876])).

fof(f3876,plain,
    ( spl4_308
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_308])])).

fof(f3882,plain,
    ( spl4_311
  <=> ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_311])])).

fof(f3820,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_34
    | ~ spl4_206 ),
    inference(superposition,[],[f373,f3130])).

fof(f3871,plain,
    ( spl4_304
    | ~ spl4_297
    | ~ spl4_307
    | ~ spl4_36
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3819,f3129,f376,f3869,f3837,f3863])).

fof(f3863,plain,
    ( spl4_304
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_304])])).

fof(f3869,plain,
    ( spl4_307
  <=> ~ r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_307])])).

fof(f3819,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_36
    | ~ spl4_206 ),
    inference(superposition,[],[f377,f3130])).

fof(f3858,plain,
    ( ~ spl4_301
    | ~ spl4_297
    | spl4_302
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3816,f3129,f372,f364,f107,f3856,f3837,f3850])).

fof(f3850,plain,
    ( spl4_301
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_301])])).

fof(f3856,plain,
    ( spl4_302
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_302])])).

fof(f3816,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),sK1)
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_206 ),
    inference(superposition,[],[f1587,f3130])).

fof(f3845,plain,
    ( ~ spl4_295
    | ~ spl4_297
    | spl4_298
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3815,f3129,f376,f368,f107,f3843,f3837,f3831])).

fof(f3831,plain,
    ( spl4_295
  <=> ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_295])])).

fof(f3843,plain,
    ( spl4_298
  <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_298])])).

fof(f3815,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_206 ),
    inference(superposition,[],[f1613,f3130])).

fof(f3771,plain,
    ( spl4_292
    | ~ spl4_280 ),
    inference(avatar_split_clause,[],[f3744,f3701,f3769])).

fof(f3769,plain,
    ( spl4_292
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_292])])).

fof(f3701,plain,
    ( spl4_280
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_280])])).

fof(f3744,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))))
    | ~ spl4_280 ),
    inference(resolution,[],[f3702,f94])).

fof(f3702,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_280 ),
    inference(avatar_component_clause,[],[f3701])).

fof(f3763,plain,
    ( spl4_290
    | ~ spl4_280 ),
    inference(avatar_split_clause,[],[f3735,f3701,f3761])).

fof(f3761,plain,
    ( spl4_290
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_290])])).

fof(f3735,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_280 ),
    inference(resolution,[],[f3702,f76])).

fof(f3754,plain,
    ( spl4_288
    | ~ spl4_4
    | ~ spl4_202
    | ~ spl4_280 ),
    inference(avatar_split_clause,[],[f3747,f3701,f3114,f114,f3752])).

fof(f3752,plain,
    ( spl4_288
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_288])])).

fof(f3114,plain,
    ( spl4_202
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f3747,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_202
    | ~ spl4_280 ),
    inference(forward_demodulation,[],[f3746,f3115])).

fof(f3115,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_202 ),
    inference(avatar_component_clause,[],[f3114])).

fof(f3746,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_280 ),
    inference(subsumption_resolution,[],[f3732,f115])).

fof(f3732,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_280 ),
    inference(resolution,[],[f3702,f81])).

fof(f3727,plain,
    ( ~ spl4_4
    | ~ spl4_198
    | spl4_281 ),
    inference(avatar_contradiction_clause,[],[f3726])).

fof(f3726,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_198
    | ~ spl4_281 ),
    inference(subsumption_resolution,[],[f3725,f115])).

fof(f3725,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_198
    | ~ spl4_281 ),
    inference(subsumption_resolution,[],[f3723,f3076])).

fof(f3723,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_281 ),
    inference(resolution,[],[f3705,f83])).

fof(f3705,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_281 ),
    inference(avatar_component_clause,[],[f3704])).

fof(f3704,plain,
    ( spl4_281
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_281])])).

fof(f3722,plain,
    ( ~ spl4_281
    | spl4_286
    | ~ spl4_4
    | ~ spl4_202 ),
    inference(avatar_split_clause,[],[f3718,f3114,f114,f3720,f3704])).

fof(f3720,plain,
    ( spl4_286
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_286])])).

fof(f3718,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_202 ),
    inference(subsumption_resolution,[],[f3698,f115])).

fof(f3698,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_202 ),
    inference(superposition,[],[f78,f3115])).

fof(f3717,plain,
    ( ~ spl4_281
    | spl4_284
    | ~ spl4_4
    | ~ spl4_202 ),
    inference(avatar_split_clause,[],[f3713,f3114,f114,f3715,f3704])).

fof(f3715,plain,
    ( spl4_284
  <=> ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).

fof(f3713,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_202 ),
    inference(subsumption_resolution,[],[f3697,f115])).

fof(f3697,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_202 ),
    inference(superposition,[],[f78,f3115])).

fof(f3712,plain,
    ( ~ spl4_281
    | spl4_282
    | ~ spl4_4
    | ~ spl4_202 ),
    inference(avatar_split_clause,[],[f3699,f3114,f114,f3710,f3704])).

fof(f3710,plain,
    ( spl4_282
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_282])])).

fof(f3699,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_202 ),
    inference(subsumption_resolution,[],[f3696,f115])).

fof(f3696,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_202 ),
    inference(superposition,[],[f79,f3115])).

fof(f3686,plain,
    ( spl4_278
    | ~ spl4_262 ),
    inference(avatar_split_clause,[],[f3659,f3573,f3684])).

fof(f3684,plain,
    ( spl4_278
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_278])])).

fof(f3573,plain,
    ( spl4_262
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_262])])).

fof(f3659,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))))
    | ~ spl4_262 ),
    inference(resolution,[],[f3574,f94])).

fof(f3574,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_262 ),
    inference(avatar_component_clause,[],[f3573])).

fof(f3678,plain,
    ( spl4_276
    | ~ spl4_262 ),
    inference(avatar_split_clause,[],[f3650,f3573,f3676])).

fof(f3676,plain,
    ( spl4_276
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_276])])).

fof(f3650,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_262 ),
    inference(resolution,[],[f3574,f76])).

fof(f3669,plain,
    ( spl4_274
    | ~ spl4_4
    | ~ spl4_106
    | ~ spl4_262 ),
    inference(avatar_split_clause,[],[f3662,f3573,f1199,f114,f3667])).

fof(f3667,plain,
    ( spl4_274
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_274])])).

fof(f1199,plain,
    ( spl4_106
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f3662,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_106
    | ~ spl4_262 ),
    inference(forward_demodulation,[],[f3661,f1200])).

fof(f1200,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f1199])).

fof(f3661,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_262 ),
    inference(subsumption_resolution,[],[f3647,f115])).

fof(f3647,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_262 ),
    inference(resolution,[],[f3574,f81])).

fof(f3638,plain,
    ( spl4_272
    | ~ spl4_264 ),
    inference(avatar_split_clause,[],[f3606,f3582,f3636])).

fof(f3606,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_264 ),
    inference(resolution,[],[f3583,f94])).

fof(f3630,plain,
    ( spl4_270
    | ~ spl4_264 ),
    inference(avatar_split_clause,[],[f3597,f3582,f3628])).

fof(f3628,plain,
    ( spl4_270
  <=> r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_270])])).

fof(f3597,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_264 ),
    inference(resolution,[],[f3583,f76])).

fof(f3623,plain,
    ( spl4_268
    | ~ spl4_4
    | ~ spl4_264 ),
    inference(avatar_split_clause,[],[f3616,f3582,f114,f3621])).

fof(f3616,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_264 ),
    inference(subsumption_resolution,[],[f3595,f115])).

fof(f3595,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_264 ),
    inference(resolution,[],[f3583,f82])).

fof(f3615,plain,
    ( spl4_266
    | ~ spl4_4
    | ~ spl4_264 ),
    inference(avatar_split_clause,[],[f3608,f3582,f114,f3613])).

fof(f3613,plain,
    ( spl4_266
  <=> k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_266])])).

fof(f3608,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_264 ),
    inference(subsumption_resolution,[],[f3594,f115])).

fof(f3594,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_264 ),
    inference(resolution,[],[f3583,f81])).

fof(f3589,plain,
    ( ~ spl4_4
    | ~ spl4_94
    | spl4_263 ),
    inference(avatar_contradiction_clause,[],[f3588])).

fof(f3588,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_94
    | ~ spl4_263 ),
    inference(subsumption_resolution,[],[f3587,f115])).

fof(f3587,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_94
    | ~ spl4_263 ),
    inference(subsumption_resolution,[],[f3585,f1135])).

fof(f1135,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1134,plain,
    ( spl4_94
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f3585,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_263 ),
    inference(resolution,[],[f3577,f83])).

fof(f3577,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_263 ),
    inference(avatar_component_clause,[],[f3576])).

fof(f3576,plain,
    ( spl4_263
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_263])])).

fof(f3584,plain,
    ( ~ spl4_263
    | spl4_264
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f3562,f658,f3582,f3576])).

fof(f658,plain,
    ( spl4_48
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f3562,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_48 ),
    inference(superposition,[],[f90,f659])).

fof(f659,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f658])).

fof(f3571,plain,
    ( spl4_260
    | ~ spl4_48
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f3561,f1031,f658,f3568])).

fof(f3568,plain,
    ( spl4_260
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_260])])).

fof(f1031,plain,
    ( spl4_80
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f3561,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_48
    | ~ spl4_80 ),
    inference(superposition,[],[f1094,f659])).

fof(f1094,plain,
    ( ! [X3] : k3_xboole_0(X3,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),X3)
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f1067,f1066])).

fof(f1066,plain,
    ( ! [X2] : k3_xboole_0(X2,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_80 ),
    inference(resolution,[],[f1032,f86])).

fof(f1032,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1031])).

fof(f1067,plain,
    ( ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),X3)
    | ~ spl4_80 ),
    inference(resolution,[],[f1032,f89])).

fof(f3570,plain,
    ( spl4_260
    | ~ spl4_48
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f3559,f1031,f658,f3568])).

fof(f3559,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_48
    | ~ spl4_80 ),
    inference(superposition,[],[f659,f1094])).

fof(f3460,plain,
    ( ~ spl4_259
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_28
    | spl4_255 ),
    inference(avatar_split_clause,[],[f3453,f3436,f358,f114,f107,f3458])).

fof(f3458,plain,
    ( spl4_259
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_259])])).

fof(f3436,plain,
    ( spl4_255
  <=> ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_255])])).

fof(f3453,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_255 ),
    inference(subsumption_resolution,[],[f3452,f115])).

fof(f3452,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_28
    | ~ spl4_255 ),
    inference(subsumption_resolution,[],[f3451,f359])).

fof(f3451,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_255 ),
    inference(subsumption_resolution,[],[f3446,f108])).

fof(f3446,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_255 ),
    inference(resolution,[],[f3437,f78])).

fof(f3437,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_255 ),
    inference(avatar_component_clause,[],[f3436])).

fof(f3450,plain,
    ( ~ spl4_143
    | ~ spl4_18
    | ~ spl4_28
    | spl4_255 ),
    inference(avatar_split_clause,[],[f3449,f3436,f358,f275,f1636])).

fof(f1636,plain,
    ( spl4_143
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f275,plain,
    ( spl4_18
  <=> ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f3449,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_255 ),
    inference(subsumption_resolution,[],[f3445,f359])).

fof(f3445,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl4_18
    | ~ spl4_255 ),
    inference(resolution,[],[f3437,f276])).

fof(f276,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f275])).

fof(f3444,plain,
    ( ~ spl4_255
    | spl4_256
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f3430,f853,f3442,f3436])).

fof(f3442,plain,
    ( spl4_256
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_256])])).

fof(f3430,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_62 ),
    inference(superposition,[],[f1288,f88])).

fof(f88,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',idempotence_k3_xboole_0)).

fof(f3419,plain,
    ( ~ spl4_253
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_28
    | spl4_247 ),
    inference(avatar_split_clause,[],[f3412,f3383,f358,f114,f107,f3417])).

fof(f3417,plain,
    ( spl4_253
  <=> ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_253])])).

fof(f3383,plain,
    ( spl4_247
  <=> ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_247])])).

fof(f3412,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_247 ),
    inference(subsumption_resolution,[],[f3411,f115])).

fof(f3411,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_28
    | ~ spl4_247 ),
    inference(subsumption_resolution,[],[f3410,f108])).

fof(f3410,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_247 ),
    inference(subsumption_resolution,[],[f3405,f359])).

fof(f3405,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_247 ),
    inference(resolution,[],[f3384,f78])).

fof(f3384,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_247 ),
    inference(avatar_component_clause,[],[f3383])).

fof(f3409,plain,
    ( ~ spl4_151
    | ~ spl4_20
    | ~ spl4_28
    | spl4_247 ),
    inference(avatar_split_clause,[],[f3408,f3383,f358,f280,f1682])).

fof(f1682,plain,
    ( spl4_151
  <=> ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).

fof(f280,plain,
    ( spl4_20
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k2_pre_topc(sK0,sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f3408,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_20
    | ~ spl4_28
    | ~ spl4_247 ),
    inference(subsumption_resolution,[],[f3404,f359])).

fof(f3404,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_20
    | ~ spl4_247 ),
    inference(resolution,[],[f3384,f281])).

fof(f281,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k2_pre_topc(sK0,sK1),X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f280])).

fof(f3399,plain,
    ( spl4_250
    | ~ spl4_62
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f3392,f1429,f853,f3397])).

fof(f3397,plain,
    ( spl4_250
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_250])])).

fof(f1429,plain,
    ( spl4_118
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f3392,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_62
    | ~ spl4_118 ),
    inference(subsumption_resolution,[],[f3378,f1430])).

fof(f1430,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f1429])).

fof(f3378,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_62 ),
    inference(superposition,[],[f1287,f854])).

fof(f3391,plain,
    ( ~ spl4_247
    | spl4_248
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f3377,f853,f3389,f3383])).

fof(f3389,plain,
    ( spl4_248
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_248])])).

fof(f3377,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_62 ),
    inference(superposition,[],[f1287,f88])).

fof(f3359,plain,
    ( spl4_244
    | ~ spl4_216 ),
    inference(avatar_split_clause,[],[f3324,f3238,f3357])).

fof(f3357,plain,
    ( spl4_244
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_244])])).

fof(f3238,plain,
    ( spl4_216
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_216])])).

fof(f3324,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_216 ),
    inference(resolution,[],[f3239,f76])).

fof(f3239,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_216 ),
    inference(avatar_component_clause,[],[f3238])).

fof(f3352,plain,
    ( spl4_242
    | ~ spl4_4
    | ~ spl4_216 ),
    inference(avatar_split_clause,[],[f3345,f3238,f114,f3350])).

fof(f3350,plain,
    ( spl4_242
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_242])])).

fof(f3345,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_216 ),
    inference(subsumption_resolution,[],[f3322,f115])).

fof(f3322,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_216 ),
    inference(resolution,[],[f3239,f82])).

fof(f3344,plain,
    ( spl4_240
    | ~ spl4_4
    | ~ spl4_50
    | ~ spl4_92
    | ~ spl4_216 ),
    inference(avatar_split_clause,[],[f3337,f3238,f1099,f666,f114,f3342])).

fof(f3342,plain,
    ( spl4_240
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_240])])).

fof(f666,plain,
    ( spl4_50
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1099,plain,
    ( spl4_92
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f3337,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_50
    | ~ spl4_92
    | ~ spl4_216 ),
    inference(forward_demodulation,[],[f3336,f667])).

fof(f667,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f666])).

fof(f3336,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_92
    | ~ spl4_216 ),
    inference(forward_demodulation,[],[f3335,f1100])).

fof(f1100,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f1099])).

fof(f3335,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_216 ),
    inference(subsumption_resolution,[],[f3321,f115])).

fof(f3321,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_216 ),
    inference(resolution,[],[f3239,f81])).

fof(f3308,plain,
    ( ~ spl4_80
    | spl4_217 ),
    inference(avatar_contradiction_clause,[],[f3307])).

fof(f3307,plain,
    ( $false
    | ~ spl4_80
    | ~ spl4_217 ),
    inference(subsumption_resolution,[],[f3305,f1032])).

fof(f3305,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_217 ),
    inference(resolution,[],[f3242,f95])).

fof(f3242,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_217 ),
    inference(avatar_component_clause,[],[f3241])).

fof(f3241,plain,
    ( spl4_217
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_217])])).

fof(f3304,plain,
    ( ~ spl4_217
    | spl4_238
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3230,f1099,f3302,f3241])).

fof(f3302,plain,
    ( spl4_238
  <=> ! [X3] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_238])])).

fof(f3230,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_92 ),
    inference(superposition,[],[f93,f1100])).

fof(f3300,plain,
    ( ~ spl4_217
    | spl4_236
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3229,f1099,f3298,f3241])).

fof(f3298,plain,
    ( spl4_236
  <=> ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_236])])).

fof(f3229,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_92 ),
    inference(superposition,[],[f93,f1100])).

fof(f3296,plain,
    ( ~ spl4_217
    | spl4_234
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3228,f1099,f3294,f3241])).

fof(f3294,plain,
    ( spl4_234
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_234])])).

fof(f3228,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_92 ),
    inference(superposition,[],[f92,f1100])).

fof(f3292,plain,
    ( ~ spl4_217
    | spl4_232
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3227,f1099,f3290,f3241])).

fof(f3290,plain,
    ( spl4_232
  <=> ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_232])])).

fof(f3227,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_92 ),
    inference(superposition,[],[f92,f1100])).

fof(f3288,plain,
    ( spl4_228
    | ~ spl4_217
    | ~ spl4_231
    | ~ spl4_34
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3224,f1099,f372,f3286,f3241,f3280])).

fof(f3280,plain,
    ( spl4_228
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f3286,plain,
    ( spl4_231
  <=> ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_231])])).

fof(f3224,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_34
    | ~ spl4_92 ),
    inference(superposition,[],[f373,f1100])).

fof(f3275,plain,
    ( spl4_224
    | ~ spl4_217
    | ~ spl4_227
    | ~ spl4_36
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3223,f1099,f376,f3273,f3241,f3267])).

fof(f3267,plain,
    ( spl4_224
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).

fof(f3273,plain,
    ( spl4_227
  <=> ~ r1_tarski(sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_227])])).

fof(f3223,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_36
    | ~ spl4_92 ),
    inference(superposition,[],[f377,f1100])).

fof(f3262,plain,
    ( ~ spl4_221
    | ~ spl4_217
    | spl4_222
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3220,f1099,f372,f364,f107,f3260,f3241,f3254])).

fof(f3254,plain,
    ( spl4_221
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_221])])).

fof(f3260,plain,
    ( spl4_222
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).

fof(f3220,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),sK1)
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_92 ),
    inference(superposition,[],[f1587,f1100])).

fof(f3249,plain,
    ( ~ spl4_215
    | ~ spl4_217
    | spl4_218
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3219,f1099,f376,f368,f107,f3247,f3241,f3235])).

fof(f3235,plain,
    ( spl4_215
  <=> ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_215])])).

fof(f3247,plain,
    ( spl4_218
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_218])])).

fof(f3219,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_92 ),
    inference(superposition,[],[f1613,f1100])).

fof(f3179,plain,
    ( spl4_212
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f3152,f3066,f3177])).

fof(f3177,plain,
    ( spl4_212
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_212])])).

fof(f3066,plain,
    ( spl4_196
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f3152,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | ~ spl4_196 ),
    inference(resolution,[],[f3067,f94])).

fof(f3067,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_196 ),
    inference(avatar_component_clause,[],[f3066])).

fof(f3171,plain,
    ( spl4_210
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f3143,f3066,f3169])).

fof(f3169,plain,
    ( spl4_210
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_210])])).

fof(f3143,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl4_196 ),
    inference(resolution,[],[f3067,f76])).

fof(f3162,plain,
    ( spl4_208
    | ~ spl4_4
    | ~ spl4_76
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f3155,f3066,f929,f114,f3160])).

fof(f3160,plain,
    ( spl4_208
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).

fof(f929,plain,
    ( spl4_76
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f3155,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_76
    | ~ spl4_196 ),
    inference(forward_demodulation,[],[f3154,f930])).

fof(f930,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f929])).

fof(f3154,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))))
    | ~ spl4_4
    | ~ spl4_196 ),
    inference(subsumption_resolution,[],[f3140,f115])).

fof(f3140,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_196 ),
    inference(resolution,[],[f3067,f81])).

fof(f3131,plain,
    ( spl4_206
    | ~ spl4_198 ),
    inference(avatar_split_clause,[],[f3099,f3075,f3129])).

fof(f3099,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_198 ),
    inference(resolution,[],[f3076,f94])).

fof(f3123,plain,
    ( spl4_204
    | ~ spl4_198 ),
    inference(avatar_split_clause,[],[f3090,f3075,f3121])).

fof(f3121,plain,
    ( spl4_204
  <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).

fof(f3090,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_198 ),
    inference(resolution,[],[f3076,f76])).

fof(f3116,plain,
    ( spl4_202
    | ~ spl4_4
    | ~ spl4_198 ),
    inference(avatar_split_clause,[],[f3109,f3075,f114,f3114])).

fof(f3109,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_198 ),
    inference(subsumption_resolution,[],[f3088,f115])).

fof(f3088,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_198 ),
    inference(resolution,[],[f3076,f82])).

fof(f3108,plain,
    ( spl4_200
    | ~ spl4_4
    | ~ spl4_198 ),
    inference(avatar_split_clause,[],[f3101,f3075,f114,f3106])).

fof(f3106,plain,
    ( spl4_200
  <=> k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f3101,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_198 ),
    inference(subsumption_resolution,[],[f3087,f115])).

fof(f3087,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_198 ),
    inference(resolution,[],[f3076,f81])).

fof(f3082,plain,
    ( ~ spl4_4
    | ~ spl4_64
    | spl4_197 ),
    inference(avatar_contradiction_clause,[],[f3081])).

fof(f3081,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_64
    | ~ spl4_197 ),
    inference(subsumption_resolution,[],[f3080,f115])).

fof(f3080,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_64
    | ~ spl4_197 ),
    inference(subsumption_resolution,[],[f3078,f865])).

fof(f3078,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_197 ),
    inference(resolution,[],[f3070,f83])).

fof(f3070,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_197 ),
    inference(avatar_component_clause,[],[f3069])).

fof(f3069,plain,
    ( spl4_197
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).

fof(f3077,plain,
    ( ~ spl4_197
    | spl4_198
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f3055,f312,f3075,f3069])).

fof(f312,plain,
    ( spl4_22
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f3055,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_22 ),
    inference(superposition,[],[f90,f313])).

fof(f313,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f312])).

fof(f3064,plain,
    ( spl4_194
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f3054,f312,f261,f3061])).

fof(f261,plain,
    ( spl4_14
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f3054,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(superposition,[],[f324,f313])).

fof(f324,plain,
    ( ! [X3] : k3_xboole_0(X3,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X3)
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f297,f296])).

fof(f296,plain,
    ( ! [X2] : k3_xboole_0(X2,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,sK1))
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f86])).

fof(f262,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f261])).

fof(f297,plain,
    ( ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X3)
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f89])).

fof(f3063,plain,
    ( spl4_194
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f3052,f312,f261,f3061])).

fof(f3052,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(superposition,[],[f313,f324])).

fof(f2906,plain,
    ( spl4_192
    | ~ spl4_164 ),
    inference(avatar_split_clause,[],[f2871,f2785,f2904])).

fof(f2904,plain,
    ( spl4_192
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f2871,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),u1_struct_0(sK0))
    | ~ spl4_164 ),
    inference(resolution,[],[f2786,f76])).

fof(f2899,plain,
    ( spl4_190
    | ~ spl4_4
    | ~ spl4_164 ),
    inference(avatar_split_clause,[],[f2892,f2785,f114,f2897])).

fof(f2892,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl4_4
    | ~ spl4_164 ),
    inference(subsumption_resolution,[],[f2869,f115])).

fof(f2869,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_164 ),
    inference(resolution,[],[f2786,f82])).

fof(f2891,plain,
    ( spl4_188
    | ~ spl4_4
    | ~ spl4_40
    | ~ spl4_60
    | ~ spl4_164 ),
    inference(avatar_split_clause,[],[f2884,f2785,f729,f415,f114,f2889])).

fof(f2889,plain,
    ( spl4_188
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f415,plain,
    ( spl4_40
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f729,plain,
    ( spl4_60
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f2884,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_4
    | ~ spl4_40
    | ~ spl4_60
    | ~ spl4_164 ),
    inference(forward_demodulation,[],[f2883,f416])).

fof(f416,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f415])).

fof(f2883,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_4
    | ~ spl4_60
    | ~ spl4_164 ),
    inference(forward_demodulation,[],[f2882,f730])).

fof(f730,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f729])).

fof(f2882,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))))
    | ~ spl4_4
    | ~ spl4_164 ),
    inference(subsumption_resolution,[],[f2868,f115])).

fof(f2868,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_164 ),
    inference(resolution,[],[f2786,f81])).

fof(f2855,plain,
    ( ~ spl4_44
    | spl4_165 ),
    inference(avatar_contradiction_clause,[],[f2854])).

fof(f2854,plain,
    ( $false
    | ~ spl4_44
    | ~ spl4_165 ),
    inference(subsumption_resolution,[],[f2852,f619])).

fof(f2852,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_165 ),
    inference(resolution,[],[f2789,f95])).

fof(f2789,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_165 ),
    inference(avatar_component_clause,[],[f2788])).

fof(f2788,plain,
    ( spl4_165
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_165])])).

fof(f2851,plain,
    ( ~ spl4_165
    | spl4_186
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2777,f729,f2849,f2788])).

fof(f2849,plain,
    ( spl4_186
  <=> ! [X3] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).

fof(f2777,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),X3))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_60 ),
    inference(superposition,[],[f93,f730])).

fof(f2847,plain,
    ( ~ spl4_165
    | spl4_184
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2776,f729,f2845,f2788])).

fof(f2845,plain,
    ( spl4_184
  <=> ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_184])])).

fof(f2776,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_60 ),
    inference(superposition,[],[f93,f730])).

fof(f2843,plain,
    ( ~ spl4_165
    | spl4_182
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2775,f729,f2841,f2788])).

fof(f2841,plain,
    ( spl4_182
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f2775,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_60 ),
    inference(superposition,[],[f92,f730])).

fof(f2839,plain,
    ( ~ spl4_165
    | spl4_180
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2774,f729,f2837,f2788])).

fof(f2837,plain,
    ( spl4_180
  <=> ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).

fof(f2774,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_60 ),
    inference(superposition,[],[f92,f730])).

fof(f2835,plain,
    ( spl4_176
    | ~ spl4_165
    | ~ spl4_179
    | ~ spl4_34
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2771,f729,f372,f2833,f2788,f2827])).

fof(f2827,plain,
    ( spl4_176
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_176])])).

fof(f2833,plain,
    ( spl4_179
  <=> ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_179])])).

fof(f2771,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_34
    | ~ spl4_60 ),
    inference(superposition,[],[f373,f730])).

fof(f2822,plain,
    ( spl4_172
    | ~ spl4_165
    | ~ spl4_175
    | ~ spl4_36
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2770,f729,f376,f2820,f2788,f2814])).

fof(f2814,plain,
    ( spl4_172
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_172])])).

fof(f2820,plain,
    ( spl4_175
  <=> ~ r1_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_175])])).

fof(f2770,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_36
    | ~ spl4_60 ),
    inference(superposition,[],[f377,f730])).

fof(f2809,plain,
    ( ~ spl4_169
    | ~ spl4_165
    | spl4_170
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2767,f729,f372,f364,f107,f2807,f2788,f2801])).

fof(f2807,plain,
    ( spl4_170
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f2767,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_60 ),
    inference(superposition,[],[f1587,f730])).

fof(f2796,plain,
    ( ~ spl4_163
    | ~ spl4_165
    | spl4_166
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f2766,f729,f376,f368,f107,f2794,f2788,f2782])).

fof(f2782,plain,
    ( spl4_163
  <=> ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_163])])).

fof(f2794,plain,
    ( spl4_166
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f2766,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_60 ),
    inference(superposition,[],[f1613,f730])).

fof(f1851,plain,
    ( spl4_160
    | ~ spl4_38
    | ~ spl4_156 ),
    inference(avatar_split_clause,[],[f1844,f1830,f407,f1849])).

fof(f1849,plain,
    ( spl4_160
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f407,plain,
    ( spl4_38
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1830,plain,
    ( spl4_156
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f1844,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_38
    | ~ spl4_156 ),
    inference(backward_demodulation,[],[f1831,f408])).

fof(f408,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f407])).

fof(f1831,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_156 ),
    inference(avatar_component_clause,[],[f1830])).

fof(f1842,plain,
    ( spl4_158
    | ~ spl4_14
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f1835,f407,f261,f1840])).

fof(f1840,plain,
    ( spl4_158
  <=> m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f1835,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f1821,f262])).

fof(f1821,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_38 ),
    inference(superposition,[],[f90,f408])).

fof(f1834,plain,
    ( spl4_156
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1833,f853,f407,f261,f1830])).

fof(f1833,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1820,f854])).

fof(f1820,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_14
    | ~ spl4_38 ),
    inference(superposition,[],[f296,f408])).

fof(f1832,plain,
    ( spl4_156
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1825,f853,f407,f261,f1830])).

fof(f1825,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f1816,f854])).

fof(f1816,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_14
    | ~ spl4_38 ),
    inference(superposition,[],[f408,f296])).

fof(f1701,plain,
    ( ~ spl4_153
    | spl4_154
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1688,f1134,f681,f376,f368,f107,f1699,f1693])).

fof(f1693,plain,
    ( spl4_153
  <=> ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).

fof(f1699,plain,
    ( spl4_154
  <=> r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f681,plain,
    ( spl4_54
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1688,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1668,f1135])).

fof(f1668,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(superposition,[],[f1613,f682])).

fof(f682,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f681])).

fof(f1687,plain,
    ( ~ spl4_149
    | spl4_150
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1674,f864,f376,f368,f329,f107,f1685,f1679])).

fof(f1679,plain,
    ( spl4_149
  <=> ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_149])])).

fof(f1685,plain,
    ( spl4_150
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f329,plain,
    ( spl4_26
  <=> k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1674,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f1667,f865])).

fof(f1667,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_36 ),
    inference(superposition,[],[f1613,f330])).

fof(f330,plain,
    ( k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f329])).

fof(f1655,plain,
    ( ~ spl4_145
    | spl4_146
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1642,f1134,f681,f372,f364,f107,f1653,f1647])).

fof(f1647,plain,
    ( spl4_145
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).

fof(f1653,plain,
    ( spl4_146
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f1642,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1)
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1622,f1135])).

fof(f1622,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1)
    | ~ spl4_2
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(superposition,[],[f1587,f682])).

fof(f1641,plain,
    ( ~ spl4_141
    | spl4_142
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1628,f864,f372,f364,f329,f107,f1639,f1633])).

fof(f1633,plain,
    ( spl4_141
  <=> ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f1639,plain,
    ( spl4_142
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f1628,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_34
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f1621,f865])).

fof(f1621,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_34 ),
    inference(superposition,[],[f1587,f330])).

fof(f1563,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_135 ),
    inference(avatar_contradiction_clause,[],[f1562])).

fof(f1562,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_135 ),
    inference(subsumption_resolution,[],[f1561,f115])).

fof(f1561,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_135 ),
    inference(subsumption_resolution,[],[f1558,f108])).

fof(f1558,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_135 ),
    inference(resolution,[],[f1542,f79])).

fof(f1542,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_135 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f1541,plain,
    ( spl4_135
  <=> ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f1557,plain,
    ( spl4_136
    | ~ spl4_139
    | ~ spl4_36
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1544,f1134,f681,f376,f1555,f1549])).

fof(f1549,plain,
    ( spl4_136
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f1555,plain,
    ( spl4_139
  <=> ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f1544,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_36
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1525,f1135])).

fof(f1525,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(superposition,[],[f377,f682])).

fof(f1543,plain,
    ( spl4_132
    | ~ spl4_135
    | ~ spl4_26
    | ~ spl4_36
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1530,f864,f376,f329,f1541,f1535])).

fof(f1530,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_26
    | ~ spl4_36
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f1524,f865])).

fof(f1524,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_26
    | ~ spl4_36 ),
    inference(superposition,[],[f377,f330])).

fof(f1515,plain,
    ( spl4_128
    | ~ spl4_131
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f1502,f372,f358,f169,f1513,f1507])).

fof(f1507,plain,
    ( spl4_128
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f1513,plain,
    ( spl4_131
  <=> ~ r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f169,plain,
    ( spl4_12
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1502,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1472,f359])).

fof(f1472,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_12
    | ~ spl4_34 ),
    inference(superposition,[],[f373,f170])).

fof(f170,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1501,plain,
    ( spl4_124
    | ~ spl4_127
    | ~ spl4_34
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1488,f1134,f681,f372,f1499,f1493])).

fof(f1493,plain,
    ( spl4_124
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f1499,plain,
    ( spl4_127
  <=> ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f1488,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl4_34
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1469,f1135])).

fof(f1469,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl4_34
    | ~ spl4_54 ),
    inference(superposition,[],[f373,f682])).

fof(f1487,plain,
    ( spl4_120
    | ~ spl4_123
    | ~ spl4_26
    | ~ spl4_34
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1474,f864,f372,f329,f1485,f1479])).

fof(f1479,plain,
    ( spl4_120
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f1485,plain,
    ( spl4_123
  <=> ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f1474,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_26
    | ~ spl4_34
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f1468,f865])).

fof(f1468,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(superposition,[],[f373,f330])).

fof(f1431,plain,
    ( spl4_118
    | ~ spl4_4
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1424,f618,f415,f114,f1429])).

fof(f1424,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_4
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1423,f115])).

fof(f1423,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1420,f619])).

fof(f1420,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_40 ),
    inference(superposition,[],[f79,f416])).

fof(f1412,plain,
    ( ~ spl4_117
    | spl4_115 ),
    inference(avatar_split_clause,[],[f1405,f1402,f1410])).

fof(f1410,plain,
    ( spl4_117
  <=> ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f1402,plain,
    ( spl4_115
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f1405,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl4_115 ),
    inference(resolution,[],[f1403,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1403,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_115 ),
    inference(avatar_component_clause,[],[f1402])).

fof(f1404,plain,
    ( spl4_112
    | ~ spl4_115
    | ~ spl4_30
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f1386,f422,f364,f1402,f1396])).

fof(f1396,plain,
    ( spl4_112
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f422,plain,
    ( spl4_42
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1386,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1)
    | ~ spl4_30
    | ~ spl4_42 ),
    inference(resolution,[],[f365,f423])).

fof(f423,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1298,plain,
    ( spl4_110
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1286,f853,f1293])).

fof(f1293,plain,
    ( spl4_110
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f1286,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_62 ),
    inference(superposition,[],[f87,f854])).

fof(f1297,plain,
    ( spl4_110
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1285,f853,f1293])).

fof(f1285,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_62 ),
    inference(superposition,[],[f87,f854])).

fof(f1296,plain,
    ( spl4_110
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1282,f853,f1293])).

fof(f1282,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_62 ),
    inference(superposition,[],[f854,f87])).

fof(f1295,plain,
    ( spl4_110
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1281,f853,f1293])).

fof(f1281,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_62 ),
    inference(superposition,[],[f854,f87])).

fof(f1208,plain,
    ( spl4_108
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1174,f1134,f1206])).

fof(f1206,plain,
    ( spl4_108
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1174,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_94 ),
    inference(resolution,[],[f1135,f76])).

fof(f1201,plain,
    ( spl4_106
    | ~ spl4_4
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1194,f1134,f114,f1199])).

fof(f1194,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1172,f115])).

fof(f1172,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_94 ),
    inference(resolution,[],[f1135,f82])).

fof(f1193,plain,
    ( spl4_104
    | ~ spl4_4
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1186,f1134,f681,f114,f1191])).

fof(f1191,plain,
    ( spl4_104
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1186,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_54
    | ~ spl4_94 ),
    inference(forward_demodulation,[],[f1185,f682])).

fof(f1185,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1171,f115])).

fof(f1171,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_94 ),
    inference(resolution,[],[f1135,f81])).

fof(f1166,plain,
    ( ~ spl4_46
    | spl4_95 ),
    inference(avatar_contradiction_clause,[],[f1165])).

fof(f1165,plain,
    ( $false
    | ~ spl4_46
    | ~ spl4_95 ),
    inference(subsumption_resolution,[],[f1163,f628])).

fof(f628,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl4_46
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f1163,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_95 ),
    inference(resolution,[],[f1138,f95])).

fof(f1138,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_95 ),
    inference(avatar_component_clause,[],[f1137])).

fof(f1137,plain,
    ( spl4_95
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f1154,plain,
    ( ~ spl4_95
    | spl4_102
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f1132,f681,f1152,f1137])).

fof(f1152,plain,
    ( spl4_102
  <=> ! [X3] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f1132,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X3))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_54 ),
    inference(superposition,[],[f93,f682])).

fof(f1150,plain,
    ( ~ spl4_95
    | spl4_100
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f1131,f681,f1148,f1137])).

fof(f1148,plain,
    ( spl4_100
  <=> ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f1131,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,sK1))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_54 ),
    inference(superposition,[],[f93,f682])).

fof(f1146,plain,
    ( ~ spl4_95
    | spl4_98
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f1130,f681,f1144,f1137])).

fof(f1144,plain,
    ( spl4_98
  <=> ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f1130,plain,
    ( ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_54 ),
    inference(superposition,[],[f92,f682])).

fof(f1142,plain,
    ( ~ spl4_95
    | spl4_96
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f1129,f681,f1140,f1137])).

fof(f1140,plain,
    ( spl4_96
  <=> ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1129,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,sK1))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_54 ),
    inference(superposition,[],[f92,f682])).

fof(f1101,plain,
    ( spl4_92
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1074,f1031,f1099])).

fof(f1074,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl4_80 ),
    inference(resolution,[],[f1032,f94])).

fof(f1093,plain,
    ( spl4_90
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1065,f1031,f1091])).

fof(f1091,plain,
    ( spl4_90
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1065,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_80 ),
    inference(resolution,[],[f1032,f76])).

fof(f1084,plain,
    ( spl4_88
    | ~ spl4_4
    | ~ spl4_50
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1077,f1031,f666,f114,f1082])).

fof(f1082,plain,
    ( spl4_88
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1077,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_50
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f1076,f667])).

fof(f1076,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f1062,f115])).

fof(f1062,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_80 ),
    inference(resolution,[],[f1032,f81])).

fof(f1057,plain,
    ( ~ spl4_4
    | ~ spl4_46
    | spl4_81 ),
    inference(avatar_contradiction_clause,[],[f1056])).

fof(f1056,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_46
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f1055,f115])).

fof(f1055,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_46
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f1053,f628])).

fof(f1053,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_81 ),
    inference(resolution,[],[f1035,f83])).

fof(f1035,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1034,plain,
    ( spl4_81
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f1052,plain,
    ( ~ spl4_81
    | spl4_86
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f1048,f666,f114,f1050,f1034])).

fof(f1050,plain,
    ( spl4_86
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1048,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1028,f115])).

fof(f1028,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_50 ),
    inference(superposition,[],[f78,f667])).

fof(f1047,plain,
    ( ~ spl4_81
    | spl4_84
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f1043,f666,f114,f1045,f1034])).

fof(f1045,plain,
    ( spl4_84
  <=> ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1043,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1027,f115])).

fof(f1027,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
        | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_50 ),
    inference(superposition,[],[f78,f667])).

fof(f1042,plain,
    ( ~ spl4_81
    | spl4_82
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f1029,f666,f114,f1040,f1034])).

fof(f1040,plain,
    ( spl4_82
  <=> r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1029,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1026,f115])).

fof(f1026,plain,
    ( r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_50 ),
    inference(superposition,[],[f79,f667])).

fof(f938,plain,
    ( spl4_78
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f903,f864,f936])).

fof(f936,plain,
    ( spl4_78
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f903,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_64 ),
    inference(resolution,[],[f865,f76])).

fof(f931,plain,
    ( spl4_76
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f924,f864,f114,f929])).

fof(f924,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f901,f115])).

fof(f901,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_64 ),
    inference(resolution,[],[f865,f82])).

fof(f923,plain,
    ( spl4_74
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_26
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f916,f864,f329,f154,f114,f921])).

fof(f921,plain,
    ( spl4_74
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f154,plain,
    ( spl4_8
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f916,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_26
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f915,f155])).

fof(f155,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f915,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f914,f330])).

fof(f914,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f900,f115])).

fof(f900,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_64 ),
    inference(resolution,[],[f865,f81])).

fof(f888,plain,
    ( ~ spl4_14
    | spl4_65 ),
    inference(avatar_contradiction_clause,[],[f887])).

fof(f887,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_65 ),
    inference(subsumption_resolution,[],[f885,f262])).

fof(f885,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_65 ),
    inference(resolution,[],[f868,f95])).

fof(f868,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f867])).

fof(f867,plain,
    ( spl4_65
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f884,plain,
    ( ~ spl4_65
    | spl4_72
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f862,f329,f882,f867])).

fof(f882,plain,
    ( spl4_72
  <=> ! [X3] :
        ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f862,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X3))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_26 ),
    inference(superposition,[],[f93,f330])).

fof(f880,plain,
    ( ~ spl4_65
    | spl4_70
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f861,f329,f878,f867])).

fof(f878,plain,
    ( spl4_70
  <=> ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f861,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),k2_pre_topc(sK0,sK1))
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_26 ),
    inference(superposition,[],[f93,f330])).

fof(f876,plain,
    ( ~ spl4_65
    | spl4_68
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f860,f329,f874,f867])).

fof(f874,plain,
    ( spl4_68
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f860,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_26 ),
    inference(superposition,[],[f92,f330])).

fof(f872,plain,
    ( ~ spl4_65
    | spl4_66
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f859,f329,f870,f867])).

fof(f870,plain,
    ( spl4_66
  <=> ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f859,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k2_pre_topc(sK0,sK1))
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_26 ),
    inference(superposition,[],[f92,f330])).

fof(f856,plain,
    ( spl4_62
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f839,f261,f146,f853])).

fof(f146,plain,
    ( spl4_6
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f839,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(superposition,[],[f147,f324])).

fof(f147,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f855,plain,
    ( spl4_62
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f830,f261,f146,f853])).

fof(f830,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(superposition,[],[f324,f147])).

fof(f731,plain,
    ( spl4_60
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f704,f618,f729])).

fof(f704,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_44 ),
    inference(resolution,[],[f619,f94])).

fof(f723,plain,
    ( spl4_58
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f695,f618,f721])).

fof(f721,plain,
    ( spl4_58
  <=> r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f695,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl4_44 ),
    inference(resolution,[],[f619,f76])).

fof(f714,plain,
    ( spl4_56
    | ~ spl4_4
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f707,f618,f415,f114,f712])).

fof(f707,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl4_4
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f706,f416])).

fof(f706,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f692,f115])).

fof(f692,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_44 ),
    inference(resolution,[],[f619,f81])).

fof(f683,plain,
    ( spl4_54
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f651,f627,f681])).

fof(f651,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl4_46 ),
    inference(resolution,[],[f628,f94])).

fof(f675,plain,
    ( spl4_52
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f642,f627,f673])).

fof(f673,plain,
    ( spl4_52
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f642,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_46 ),
    inference(resolution,[],[f628,f76])).

fof(f668,plain,
    ( spl4_50
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f661,f627,f114,f666])).

fof(f661,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f640,f115])).

fof(f640,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_46 ),
    inference(resolution,[],[f628,f82])).

fof(f660,plain,
    ( spl4_48
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f653,f627,f114,f658])).

fof(f653,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f639,f115])).

fof(f639,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_46 ),
    inference(resolution,[],[f628,f81])).

fof(f634,plain,
    ( ~ spl4_4
    | ~ spl4_28
    | spl4_45 ),
    inference(avatar_contradiction_clause,[],[f633])).

fof(f633,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_28
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f632,f115])).

fof(f632,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_28
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f630,f359])).

fof(f630,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_45 ),
    inference(resolution,[],[f622,f83])).

fof(f622,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl4_45
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f629,plain,
    ( ~ spl4_45
    | spl4_46
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f615,f146,f627,f621])).

fof(f615,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(superposition,[],[f90,f147])).

fof(f424,plain,
    ( spl4_42
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f390,f358,f422])).

fof(f390,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_28 ),
    inference(resolution,[],[f359,f76])).

fof(f417,plain,
    ( spl4_40
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f410,f358,f114,f415])).

fof(f410,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f388,f115])).

fof(f388,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f359,f82])).

fof(f409,plain,
    ( spl4_38
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f402,f358,f169,f114,f407])).

fof(f402,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f401,f170])).

fof(f401,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f387,f115])).

fof(f387,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f359,f81])).

fof(f382,plain,
    ( ~ spl4_2
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f379,f108])).

fof(f379,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_29 ),
    inference(resolution,[],[f362,f95])).

fof(f362,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl4_29
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f378,plain,
    ( ~ spl4_29
    | spl4_36
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f356,f169,f376,f361])).

fof(f356,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X3))
        | r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_12 ),
    inference(superposition,[],[f93,f170])).

fof(f374,plain,
    ( ~ spl4_29
    | spl4_34
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f355,f169,f372,f361])).

fof(f355,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X2),sK1)
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_12 ),
    inference(superposition,[],[f93,f170])).

fof(f370,plain,
    ( ~ spl4_29
    | spl4_32
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f354,f169,f368,f361])).

fof(f354,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_12 ),
    inference(superposition,[],[f92,f170])).

fof(f366,plain,
    ( ~ spl4_29
    | spl4_30
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f353,f169,f364,f361])).

fof(f353,plain,
    ( ! [X0] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),sK1)
        | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_12 ),
    inference(superposition,[],[f92,f170])).

fof(f331,plain,
    ( spl4_26
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f304,f261,f329])).

fof(f304,plain,
    ( k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f94])).

fof(f323,plain,
    ( spl4_24
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f295,f261,f321])).

fof(f321,plain,
    ( spl4_24
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f295,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f76])).

fof(f314,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f307,f261,f154,f114,f312])).

fof(f307,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f306,f155])).

fof(f306,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f292,f115])).

fof(f292,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f262,f81])).

fof(f287,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f285,f115])).

fof(f285,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f283,f108])).

fof(f283,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f265,f83])).

fof(f265,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl4_15
  <=> ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f282,plain,
    ( ~ spl4_15
    | spl4_20
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f278,f154,f114,f280,f264])).

fof(f278,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,sK1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f258,f115])).

fof(f258,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(k2_pre_topc(sK0,sK1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_8 ),
    inference(superposition,[],[f78,f155])).

fof(f277,plain,
    ( ~ spl4_15
    | spl4_18
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f273,f154,f114,f275,f264])).

fof(f273,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f257,f115])).

fof(f257,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_8 ),
    inference(superposition,[],[f78,f155])).

fof(f272,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f259,f154,f114,f270,f264])).

fof(f270,plain,
    ( spl4_16
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f259,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f256,f115])).

fof(f256,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(superposition,[],[f79,f155])).

fof(f171,plain,
    ( spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f139,f107,f169])).

fof(f139,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_2 ),
    inference(resolution,[],[f108,f94])).

fof(f163,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f130,f107,f161])).

fof(f161,plain,
    ( spl4_10
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f130,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f108,f76])).

fof(f156,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f149,f114,f107,f154])).

fof(f149,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f128,f115])).

fof(f128,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f108,f82])).

fof(f148,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f141,f114,f107,f146])).

fof(f141,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f127,f115])).

fof(f127,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f108,f81])).

fof(f116,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f72,f114])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f64,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,sK1)),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t72_tops_1.p',t72_tops_1)).

fof(f109,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f73,f107])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f74,f100])).

fof(f74,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
