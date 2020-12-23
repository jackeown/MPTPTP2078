%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1847+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 168 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :    8
%              Number of atoms          :  285 ( 688 expanded)
%              Number of equality atoms :   47 ( 114 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6927,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5579,f5583,f5587,f5591,f5595,f5599,f5665,f5673,f5711,f5840,f5883,f6249,f6296,f6379,f6924,f6926])).

fof(f6926,plain,
    ( u1_struct_0(sK92) != u1_struct_0(sK90)
    | u1_struct_0(sK91) != u1_struct_0(sK90)
    | v1_subset_1(u1_struct_0(sK92),u1_struct_0(sK90))
    | ~ v1_subset_1(u1_struct_0(sK91),u1_struct_0(sK90)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6924,plain,
    ( spl210_78
    | ~ spl210_51
    | ~ spl210_67 ),
    inference(avatar_split_clause,[],[f6923,f5928,f5838,f5982])).

fof(f5982,plain,
    ( spl210_78
  <=> u1_struct_0(sK91) = u1_struct_0(sK90) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_78])])).

fof(f5838,plain,
    ( spl210_51
  <=> ! [X36,X37] :
        ( g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) != g1_pre_topc(X36,X37)
        | u1_struct_0(sK92) = X36 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_51])])).

fof(f5928,plain,
    ( spl210_67
  <=> u1_struct_0(sK92) = u1_struct_0(sK90) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_67])])).

fof(f6923,plain,
    ( u1_struct_0(sK91) = u1_struct_0(sK90)
    | ~ spl210_51
    | ~ spl210_67 ),
    inference(forward_demodulation,[],[f6922,f5929])).

fof(f5929,plain,
    ( u1_struct_0(sK92) = u1_struct_0(sK90)
    | ~ spl210_67 ),
    inference(avatar_component_clause,[],[f5928])).

fof(f6922,plain,
    ( u1_struct_0(sK91) = u1_struct_0(sK92)
    | ~ spl210_51 ),
    inference(equality_resolution,[],[f5839])).

fof(f5839,plain,
    ( ! [X37,X36] :
        ( g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) != g1_pre_topc(X36,X37)
        | u1_struct_0(sK92) = X36 )
    | ~ spl210_51 ),
    inference(avatar_component_clause,[],[f5838])).

fof(f6379,plain,
    ( ~ spl210_6
    | ~ spl210_5
    | spl210_117
    | ~ spl210_2
    | ~ spl210_26 ),
    inference(avatar_split_clause,[],[f6317,f5709,f5581,f6374,f5593,f5597])).

fof(f5597,plain,
    ( spl210_6
  <=> l1_pre_topc(sK90) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_6])])).

fof(f5593,plain,
    ( spl210_5
  <=> m1_pre_topc(sK91,sK90) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_5])])).

fof(f6374,plain,
    ( spl210_117
  <=> v1_subset_1(u1_struct_0(sK91),u1_struct_0(sK90)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_117])])).

fof(f5581,plain,
    ( spl210_2
  <=> v1_tex_2(sK91,sK90) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_2])])).

fof(f5709,plain,
    ( spl210_26
  <=> m1_subset_1(u1_struct_0(sK91),k1_zfmisc_1(u1_struct_0(sK90))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_26])])).

fof(f6317,plain,
    ( ~ v1_tex_2(sK91,sK90)
    | v1_subset_1(u1_struct_0(sK91),u1_struct_0(sK90))
    | ~ m1_pre_topc(sK91,sK90)
    | ~ l1_pre_topc(sK90)
    | ~ spl210_26 ),
    inference(resolution,[],[f5710,f5518])).

fof(f5518,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f4689])).

fof(f4689,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4247])).

fof(f4247,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3616])).

fof(f3616,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3615])).

fof(f3615,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3594])).

fof(f3594,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

fof(f5710,plain,
    ( m1_subset_1(u1_struct_0(sK91),k1_zfmisc_1(u1_struct_0(sK90)))
    | ~ spl210_26 ),
    inference(avatar_component_clause,[],[f5709])).

fof(f6296,plain,
    ( spl210_101
    | spl210_67
    | ~ spl210_18 ),
    inference(avatar_split_clause,[],[f6213,f5663,f5928,f6243])).

fof(f6243,plain,
    ( spl210_101
  <=> v1_subset_1(u1_struct_0(sK92),u1_struct_0(sK90)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_101])])).

fof(f5663,plain,
    ( spl210_18
  <=> m1_subset_1(u1_struct_0(sK92),k1_zfmisc_1(u1_struct_0(sK90))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_18])])).

fof(f6213,plain,
    ( u1_struct_0(sK92) = u1_struct_0(sK90)
    | v1_subset_1(u1_struct_0(sK92),u1_struct_0(sK90))
    | ~ spl210_18 ),
    inference(resolution,[],[f5664,f4815])).

fof(f4815,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f4318])).

fof(f4318,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f3687])).

fof(f3687,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3568])).

fof(f3568,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f5664,plain,
    ( m1_subset_1(u1_struct_0(sK92),k1_zfmisc_1(u1_struct_0(sK90)))
    | ~ spl210_18 ),
    inference(avatar_component_clause,[],[f5663])).

fof(f6249,plain,
    ( ~ spl210_6
    | ~ spl210_4
    | spl210_1
    | ~ spl210_101
    | ~ spl210_18 ),
    inference(avatar_split_clause,[],[f6185,f5663,f6243,f5577,f5589,f5597])).

fof(f5589,plain,
    ( spl210_4
  <=> m1_pre_topc(sK92,sK90) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_4])])).

fof(f5577,plain,
    ( spl210_1
  <=> v1_tex_2(sK92,sK90) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_1])])).

fof(f6185,plain,
    ( ~ v1_subset_1(u1_struct_0(sK92),u1_struct_0(sK90))
    | v1_tex_2(sK92,sK90)
    | ~ m1_pre_topc(sK92,sK90)
    | ~ l1_pre_topc(sK90)
    | ~ spl210_18 ),
    inference(resolution,[],[f5664,f5519])).

fof(f5519,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f4688])).

fof(f4688,plain,(
    ! [X2,X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4247])).

fof(f5883,plain,
    ( spl210_50
    | ~ spl210_20 ),
    inference(avatar_split_clause,[],[f5873,f5671,f5835])).

fof(f5835,plain,
    ( spl210_50
  <=> m1_subset_1(u1_pre_topc(sK92),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK92)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_50])])).

fof(f5671,plain,
    ( spl210_20
  <=> l1_pre_topc(sK92) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_20])])).

fof(f5873,plain,
    ( m1_subset_1(u1_pre_topc(sK92),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK92))))
    | ~ spl210_20 ),
    inference(resolution,[],[f5672,f4798])).

fof(f4798,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f3669])).

fof(f3669,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f5672,plain,
    ( l1_pre_topc(sK92)
    | ~ spl210_20 ),
    inference(avatar_component_clause,[],[f5671])).

fof(f5840,plain,
    ( ~ spl210_50
    | spl210_51
    | ~ spl210_3 ),
    inference(avatar_split_clause,[],[f5756,f5585,f5838,f5835])).

fof(f5585,plain,
    ( spl210_3
  <=> g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) = g1_pre_topc(u1_struct_0(sK92),u1_pre_topc(sK92)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl210_3])])).

fof(f5756,plain,
    ( ! [X37,X36] :
        ( g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) != g1_pre_topc(X36,X37)
        | u1_struct_0(sK92) = X36
        | ~ m1_subset_1(u1_pre_topc(sK92),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK92)))) )
    | ~ spl210_3 ),
    inference(superposition,[],[f4699,f5586])).

fof(f5586,plain,
    ( g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) = g1_pre_topc(u1_struct_0(sK92),u1_pre_topc(sK92))
    | ~ spl210_3 ),
    inference(avatar_component_clause,[],[f5585])).

fof(f4699,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3621])).

fof(f3621,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1808])).

fof(f1808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f5711,plain,
    ( ~ spl210_6
    | spl210_26
    | ~ spl210_5 ),
    inference(avatar_split_clause,[],[f5700,f5593,f5709,f5597])).

fof(f5700,plain,
    ( m1_subset_1(u1_struct_0(sK91),k1_zfmisc_1(u1_struct_0(sK90)))
    | ~ l1_pre_topc(sK90)
    | ~ spl210_5 ),
    inference(resolution,[],[f5594,f4809])).

fof(f4809,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3683])).

fof(f3683,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3441])).

fof(f3441,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f5594,plain,
    ( m1_pre_topc(sK91,sK90)
    | ~ spl210_5 ),
    inference(avatar_component_clause,[],[f5593])).

fof(f5673,plain,
    ( ~ spl210_6
    | spl210_20
    | ~ spl210_4 ),
    inference(avatar_split_clause,[],[f5623,f5589,f5671,f5597])).

fof(f5623,plain,
    ( l1_pre_topc(sK92)
    | ~ l1_pre_topc(sK90)
    | ~ spl210_4 ),
    inference(resolution,[],[f5590,f4811])).

fof(f4811,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3685])).

fof(f3685,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f5590,plain,
    ( m1_pre_topc(sK92,sK90)
    | ~ spl210_4 ),
    inference(avatar_component_clause,[],[f5589])).

fof(f5665,plain,
    ( ~ spl210_6
    | spl210_18
    | ~ spl210_4 ),
    inference(avatar_split_clause,[],[f5621,f5589,f5663,f5597])).

fof(f5621,plain,
    ( m1_subset_1(u1_struct_0(sK92),k1_zfmisc_1(u1_struct_0(sK90)))
    | ~ l1_pre_topc(sK90)
    | ~ spl210_4 ),
    inference(resolution,[],[f5590,f4809])).

fof(f5599,plain,(
    spl210_6 ),
    inference(avatar_split_clause,[],[f4682,f5597])).

fof(f4682,plain,(
    l1_pre_topc(sK90) ),
    inference(cnf_transformation,[],[f4246])).

fof(f4246,plain,
    ( ~ v1_tex_2(sK92,sK90)
    & v1_tex_2(sK91,sK90)
    & g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) = g1_pre_topc(u1_struct_0(sK92),u1_pre_topc(sK92))
    & m1_pre_topc(sK92,sK90)
    & m1_pre_topc(sK91,sK90)
    & l1_pre_topc(sK90) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK90,sK91,sK92])],[f3614,f4245,f4244,f4243])).

fof(f4243,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK90)
              & v1_tex_2(X1,sK90)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK90) )
          & m1_pre_topc(X1,sK90) )
      & l1_pre_topc(sK90) ) ),
    introduced(choice_axiom,[])).

fof(f4244,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK90)
            & v1_tex_2(X1,sK90)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK90) )
        & m1_pre_topc(X1,sK90) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK90)
          & v1_tex_2(sK91,sK90)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91))
          & m1_pre_topc(X2,sK90) )
      & m1_pre_topc(sK91,sK90) ) ),
    introduced(choice_axiom,[])).

fof(f4245,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK90)
        & v1_tex_2(sK91,sK90)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91))
        & m1_pre_topc(X2,sK90) )
   => ( ~ v1_tex_2(sK92,sK90)
      & v1_tex_2(sK91,sK90)
      & g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) = g1_pre_topc(u1_struct_0(sK92),u1_pre_topc(sK92))
      & m1_pre_topc(sK92,sK90) ) ),
    introduced(choice_axiom,[])).

fof(f3614,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3613])).

fof(f3613,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3596])).

fof(f3596,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3595])).

fof(f3595,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

fof(f5595,plain,(
    spl210_5 ),
    inference(avatar_split_clause,[],[f4683,f5593])).

fof(f4683,plain,(
    m1_pre_topc(sK91,sK90) ),
    inference(cnf_transformation,[],[f4246])).

fof(f5591,plain,(
    spl210_4 ),
    inference(avatar_split_clause,[],[f4684,f5589])).

fof(f4684,plain,(
    m1_pre_topc(sK92,sK90) ),
    inference(cnf_transformation,[],[f4246])).

fof(f5587,plain,(
    spl210_3 ),
    inference(avatar_split_clause,[],[f4685,f5585])).

fof(f4685,plain,(
    g1_pre_topc(u1_struct_0(sK91),u1_pre_topc(sK91)) = g1_pre_topc(u1_struct_0(sK92),u1_pre_topc(sK92)) ),
    inference(cnf_transformation,[],[f4246])).

fof(f5583,plain,(
    spl210_2 ),
    inference(avatar_split_clause,[],[f4686,f5581])).

fof(f4686,plain,(
    v1_tex_2(sK91,sK90) ),
    inference(cnf_transformation,[],[f4246])).

fof(f5579,plain,(
    ~ spl210_1 ),
    inference(avatar_split_clause,[],[f4687,f5577])).

fof(f4687,plain,(
    ~ v1_tex_2(sK92,sK90) ),
    inference(cnf_transformation,[],[f4246])).
%------------------------------------------------------------------------------
