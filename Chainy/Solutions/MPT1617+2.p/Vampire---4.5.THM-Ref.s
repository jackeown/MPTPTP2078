%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1617+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 125 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 453 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3877,f3878,f3883,f3888,f3922,f4044,f4236,f5083,f5084,f5103])).

fof(f5103,plain,
    ( ~ spl72_4
    | ~ spl72_3
    | ~ spl72_27
    | spl72_1 ),
    inference(avatar_split_clause,[],[f5091,f3870,f4041,f3880,f3885])).

fof(f3885,plain,
    ( spl72_4
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_4])])).

fof(f3880,plain,
    ( spl72_3
  <=> m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_3])])).

fof(f4041,plain,
    ( spl72_27
  <=> r1_tarski(sK10,u1_pre_topc(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_27])])).

fof(f3870,plain,
    ( spl72_1
  <=> v1_tops_2(sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_1])])).

fof(f5091,plain,
    ( ~ r1_tarski(sK10,u1_pre_topc(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    | ~ l1_pre_topc(sK9)
    | spl72_1 ),
    inference(resolution,[],[f3590,f3872])).

fof(f3872,plain,
    ( ~ v1_tops_2(sK10,sK9)
    | spl72_1 ),
    inference(avatar_component_clause,[],[f3870])).

fof(f3590,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3391])).

fof(f3391,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3189])).

fof(f3189,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2432])).

fof(f2432,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f5084,plain,
    ( ~ spl72_8
    | spl72_2 ),
    inference(avatar_split_clause,[],[f4228,f3874,f3919])).

fof(f3919,plain,
    ( spl72_8
  <=> m1_subset_1(sK10,k1_zfmisc_1(u1_pre_topc(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_8])])).

fof(f3874,plain,
    ( spl72_2
  <=> m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK9),k1_yellow_1(u1_pre_topc(sK9)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_2])])).

fof(f4228,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_pre_topc(sK9)))
    | spl72_2 ),
    inference(forward_demodulation,[],[f3876,f3817])).

fof(f3817,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(definition_unfolding,[],[f3520,f3522])).

fof(f3522,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3074])).

fof(f3074,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f3520,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3103])).

fof(f3103,axiom,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f3876,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK9),k1_yellow_1(u1_pre_topc(sK9))))))
    | spl72_2 ),
    inference(avatar_component_clause,[],[f3874])).

fof(f5083,plain,
    ( ~ spl72_3
    | ~ spl72_1
    | ~ spl72_4
    | spl72_27 ),
    inference(avatar_split_clause,[],[f5072,f4041,f3885,f3870,f3880])).

fof(f5072,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    | ~ spl72_1
    | ~ spl72_4
    | spl72_27 ),
    inference(unit_resulting_resolution,[],[f3887,f3871,f4042,f3589])).

fof(f3589,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f3391])).

fof(f4042,plain,
    ( ~ r1_tarski(sK10,u1_pre_topc(sK9))
    | spl72_27 ),
    inference(avatar_component_clause,[],[f4041])).

fof(f3871,plain,
    ( v1_tops_2(sK10,sK9)
    | ~ spl72_1 ),
    inference(avatar_component_clause,[],[f3870])).

fof(f3887,plain,
    ( l1_pre_topc(sK9)
    | ~ spl72_4 ),
    inference(avatar_component_clause,[],[f3885])).

fof(f4236,plain,
    ( ~ spl72_27
    | spl72_8 ),
    inference(avatar_split_clause,[],[f4231,f3919,f4041])).

fof(f4231,plain,
    ( ~ r1_tarski(sK10,u1_pre_topc(sK9))
    | spl72_8 ),
    inference(resolution,[],[f3920,f3673])).

fof(f3673,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3433])).

fof(f3433,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3920,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_pre_topc(sK9)))
    | spl72_8 ),
    inference(avatar_component_clause,[],[f3919])).

fof(f4044,plain,
    ( spl72_27
    | ~ spl72_8 ),
    inference(avatar_split_clause,[],[f4031,f3919,f4041])).

fof(f4031,plain,
    ( r1_tarski(sK10,u1_pre_topc(sK9))
    | ~ spl72_8 ),
    inference(unit_resulting_resolution,[],[f3921,f3672])).

fof(f3672,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3433])).

fof(f3921,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_pre_topc(sK9)))
    | ~ spl72_8 ),
    inference(avatar_component_clause,[],[f3919])).

fof(f3922,plain,
    ( spl72_8
    | ~ spl72_2 ),
    inference(avatar_split_clause,[],[f3917,f3874,f3919])).

fof(f3917,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_pre_topc(sK9)))
    | ~ spl72_2 ),
    inference(forward_demodulation,[],[f3875,f3817])).

fof(f3875,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK9),k1_yellow_1(u1_pre_topc(sK9))))))
    | ~ spl72_2 ),
    inference(avatar_component_clause,[],[f3874])).

fof(f3888,plain,(
    spl72_4 ),
    inference(avatar_split_clause,[],[f3498,f3885])).

fof(f3498,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f3350])).

fof(f3350,plain,
    ( ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
      | ~ v1_tops_2(sK10,sK9) )
    & ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
      | v1_tops_2(sK10,sK9) )
    & m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f3347,f3349,f3348])).

fof(f3348,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | ~ v1_tops_2(X1,X0) )
            & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
            | ~ v1_tops_2(X1,sK9) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
            | v1_tops_2(X1,sK9) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) )
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f3349,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
          | ~ v1_tops_2(X1,sK9) )
        & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
          | v1_tops_2(X1,sK9) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) )
   => ( ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
        | ~ v1_tops_2(sK10,sK9) )
      & ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
        | v1_tops_2(sK10,sK9) )
      & m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) ) ),
    introduced(choice_axiom,[])).

fof(f3347,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3346])).

fof(f3346,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3137])).

fof(f3137,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3136])).

fof(f3136,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3110])).

fof(f3110,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(negated_conjecture,[],[f3109])).

fof(f3109,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_1)).

fof(f3883,plain,(
    spl72_3 ),
    inference(avatar_split_clause,[],[f3499,f3880])).

fof(f3499,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) ),
    inference(cnf_transformation,[],[f3350])).

fof(f3878,plain,
    ( spl72_1
    | spl72_2 ),
    inference(avatar_split_clause,[],[f3798,f3874,f3870])).

fof(f3798,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK9),k1_yellow_1(u1_pre_topc(sK9))))))
    | v1_tops_2(sK10,sK9) ),
    inference(definition_unfolding,[],[f3500,f3522])).

fof(f3500,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
    | v1_tops_2(sK10,sK9) ),
    inference(cnf_transformation,[],[f3350])).

fof(f3877,plain,
    ( ~ spl72_1
    | ~ spl72_2 ),
    inference(avatar_split_clause,[],[f3797,f3874,f3870])).

fof(f3797,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK9),k1_yellow_1(u1_pre_topc(sK9))))))
    | ~ v1_tops_2(sK10,sK9) ),
    inference(definition_unfolding,[],[f3501,f3522])).

fof(f3501,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK9)))))
    | ~ v1_tops_2(sK10,sK9) ),
    inference(cnf_transformation,[],[f3350])).
%------------------------------------------------------------------------------
