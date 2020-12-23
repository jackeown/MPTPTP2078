%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1702+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 5.91s
% Output     : Refutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 112 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  236 ( 360 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5363,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3788,f3804,f3862,f3872,f4243,f4250,f4586,f5341,f5359,f5362])).

fof(f5362,plain,
    ( spl38_3
    | ~ spl38_56 ),
    inference(avatar_contradiction_clause,[],[f5361])).

fof(f5361,plain,
    ( $false
    | spl38_3
    | ~ spl38_56 ),
    inference(subsumption_resolution,[],[f3857,f4593])).

fof(f4593,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl38_56 ),
    inference(resolution,[],[f4585,f3573])).

fof(f3573,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3347])).

fof(f3347,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f4585,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ spl38_56 ),
    inference(avatar_component_clause,[],[f4583])).

fof(f4583,plain,
    ( spl38_56
  <=> m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_56])])).

fof(f3857,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | spl38_3 ),
    inference(avatar_component_clause,[],[f3855])).

fof(f3855,plain,
    ( spl38_3
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_3])])).

fof(f5359,plain,
    ( ~ spl38_1
    | spl38_4
    | ~ spl38_38
    | ~ spl38_39
    | ~ spl38_40 ),
    inference(avatar_contradiction_clause,[],[f5358])).

fof(f5358,plain,
    ( $false
    | ~ spl38_1
    | spl38_4
    | ~ spl38_38
    | ~ spl38_39
    | ~ spl38_40 ),
    inference(subsumption_resolution,[],[f5357,f4242])).

fof(f4242,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ spl38_39 ),
    inference(avatar_component_clause,[],[f4240])).

fof(f4240,plain,
    ( spl38_39
  <=> g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_39])])).

fof(f5357,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ spl38_1
    | spl38_4
    | ~ spl38_38
    | ~ spl38_40 ),
    inference(subsumption_resolution,[],[f5354,f3861])).

fof(f3861,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4)
    | spl38_4 ),
    inference(avatar_component_clause,[],[f3859])).

fof(f3859,plain,
    ( spl38_4
  <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_4])])).

fof(f5354,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ spl38_1
    | ~ spl38_38
    | ~ spl38_40 ),
    inference(resolution,[],[f4237,f4258])).

fof(f4258,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_pre_topc(X0,sK4)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) )
    | ~ spl38_1
    | ~ spl38_40 ),
    inference(trivial_inequality_removal,[],[f4251])).

fof(f4251,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK4)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) )
    | ~ spl38_1
    | ~ spl38_40 ),
    inference(resolution,[],[f4249,f3787])).

fof(f3787,plain,
    ( l1_pre_topc(sK4)
    | ~ spl38_1 ),
    inference(avatar_component_clause,[],[f3785])).

fof(f3785,plain,
    ( spl38_1
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_1])])).

fof(f4249,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) )
    | ~ spl38_40 ),
    inference(avatar_component_clause,[],[f4248])).

fof(f4248,plain,
    ( spl38_40
  <=> ! [X1,X0] :
        ( m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_40])])).

fof(f4237,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl38_38 ),
    inference(avatar_component_clause,[],[f4236])).

fof(f4236,plain,
    ( spl38_38
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_38])])).

fof(f5341,plain,
    ( spl38_38
    | ~ spl38_56 ),
    inference(avatar_split_clause,[],[f4594,f4583,f4236])).

fof(f4594,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl38_56 ),
    inference(resolution,[],[f4585,f3574])).

fof(f3574,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3347])).

fof(f4586,plain,
    ( spl38_56
    | ~ spl38_6 ),
    inference(avatar_split_clause,[],[f3881,f3869,f4583])).

fof(f3869,plain,
    ( spl38_6
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_6])])).

fof(f3881,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ spl38_6 ),
    inference(resolution,[],[f3871,f3699])).

fof(f3699,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f3404])).

fof(f3404,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3871,plain,
    ( l1_pre_topc(sK5)
    | ~ spl38_6 ),
    inference(avatar_component_clause,[],[f3869])).

fof(f4250,plain,
    ( ~ spl38_6
    | spl38_40
    | ~ spl38_1
    | ~ spl38_2 ),
    inference(avatar_split_clause,[],[f3828,f3801,f3785,f4248,f3869])).

fof(f3801,plain,
    ( spl38_2
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_2])])).

fof(f3828,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(X0,X1)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK5)
        | ~ l1_pre_topc(X1) )
    | ~ spl38_1
    | ~ spl38_2 ),
    inference(subsumption_resolution,[],[f3805,f3787])).

fof(f3805,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(X0,X1)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK5)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK4) )
    | ~ spl38_2 ),
    inference(resolution,[],[f3803,f3616])).

fof(f3616,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3380])).

fof(f3380,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3379])).

fof(f3379,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1831])).

fof(f1831,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f3803,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl38_2 ),
    inference(avatar_component_clause,[],[f3801])).

fof(f4243,plain,
    ( ~ spl38_38
    | spl38_39
    | ~ spl38_3 ),
    inference(avatar_split_clause,[],[f4047,f3855,f4240,f4236])).

fof(f4047,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl38_3 ),
    inference(resolution,[],[f3856,f3589])).

fof(f3589,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3360])).

fof(f3360,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3359])).

fof(f3359,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f3856,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl38_3 ),
    inference(avatar_component_clause,[],[f3855])).

fof(f3872,plain,
    ( spl38_6
    | ~ spl38_1
    | ~ spl38_2 ),
    inference(avatar_split_clause,[],[f3846,f3801,f3785,f3869])).

fof(f3846,plain,
    ( l1_pre_topc(sK5)
    | ~ spl38_1
    | ~ spl38_2 ),
    inference(subsumption_resolution,[],[f3823,f3787])).

fof(f3823,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ spl38_2 ),
    inference(resolution,[],[f3803,f3742])).

fof(f3742,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3444])).

fof(f3444,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f3862,plain,
    ( ~ spl38_3
    | ~ spl38_4 ),
    inference(avatar_split_clause,[],[f3548,f3859,f3855])).

fof(f3548,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4)
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f3454])).

fof(f3454,plain,
    ( ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) )
    & m1_pre_topc(sK5,sK4)
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3336,f3453,f3452])).

fof(f3452,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
              | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK4)
            | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          & m1_pre_topc(X1,sK4) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3453,plain,
    ( ? [X1] :
        ( ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK4)
          | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
        & m1_pre_topc(X1,sK4) )
   => ( ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4)
        | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) )
      & m1_pre_topc(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3336,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3328])).

fof(f3328,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
              & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    inference(negated_conjecture,[],[f3327])).

fof(f3327,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f3804,plain,(
    spl38_2 ),
    inference(avatar_split_clause,[],[f3547,f3801])).

fof(f3547,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f3454])).

fof(f3788,plain,(
    spl38_1 ),
    inference(avatar_split_clause,[],[f3546,f3785])).

fof(f3546,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3454])).
%------------------------------------------------------------------------------
