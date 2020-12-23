%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1320+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 4.98s
% Output     : Refutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 509 expanded)
%              Number of leaves         :   87 ( 202 expanded)
%              Depth                    :   14
%              Number of atoms          :  660 (1313 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5011,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4445,f4450,f4455,f4460,f4465,f4470,f4479,f4500,f4507,f4514,f4519,f4524,f4529,f4534,f4539,f4544,f4549,f4554,f4559,f4572,f4581,f4586,f4601,f4616,f4628,f4633,f4638,f4684,f4690,f4700,f4705,f4715,f4720,f4734,f4743,f4748,f4753,f4758,f4770,f4784,f4816,f4832,f4841,f4862,f4895,f4904,f4909,f4914,f4940,f4975,f4979,f4984,f5008])).

fof(f5008,plain,
    ( ~ spl180_1
    | ~ spl180_3
    | spl180_4
    | ~ spl180_5
    | ~ spl180_6 ),
    inference(avatar_contradiction_clause,[],[f5007])).

fof(f5007,plain,
    ( $false
    | ~ spl180_1
    | ~ spl180_3
    | spl180_4
    | ~ spl180_5
    | ~ spl180_6 ),
    inference(subsumption_resolution,[],[f5006,f4444])).

fof(f4444,plain,
    ( l1_pre_topc(sK0)
    | ~ spl180_1 ),
    inference(avatar_component_clause,[],[f4442])).

fof(f4442,plain,
    ( spl180_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_1])])).

fof(f5006,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl180_3
    | spl180_4
    | ~ spl180_5
    | ~ spl180_6 ),
    inference(subsumption_resolution,[],[f5005,f4464])).

fof(f4464,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl180_5 ),
    inference(avatar_component_clause,[],[f4462])).

fof(f4462,plain,
    ( spl180_5
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_5])])).

fof(f5005,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl180_3
    | spl180_4
    | ~ spl180_6 ),
    inference(subsumption_resolution,[],[f5004,f4469])).

fof(f4469,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl180_6 ),
    inference(avatar_component_clause,[],[f4467])).

fof(f4467,plain,
    ( spl180_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_6])])).

fof(f5004,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl180_3
    | spl180_4 ),
    inference(subsumption_resolution,[],[f4990,f4454])).

fof(f4454,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl180_3 ),
    inference(avatar_component_clause,[],[f4452])).

fof(f4452,plain,
    ( spl180_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_3])])).

fof(f4990,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | spl180_4 ),
    inference(resolution,[],[f4483,f4459])).

fof(f4459,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    | spl180_4 ),
    inference(avatar_component_clause,[],[f4457])).

fof(f4457,plain,
    ( spl180_4
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_4])])).

fof(f4483,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X5,X1),k1_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(X5,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f4482,f3213])).

fof(f3213,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f2432])).

fof(f2432,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f2431])).

fof(f2431,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f4482,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X5,X1),k1_tops_2(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f4471,f3244])).

fof(f3244,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ),
    inference(cnf_transformation,[],[f2459])).

fof(f2459,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2375])).

fof(f2375,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

fof(f4471,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X5,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X5,X1),k1_tops_2(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f4327,f3181])).

fof(f3181,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2402])).

fof(f2402,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2401])).

fof(f2401,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2248])).

fof(f2248,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f4327,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X5,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X5,X1),k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f4326])).

fof(f4326,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X5,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X5,X1),X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f3185])).

fof(f3185,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X2)
      | k9_subset_1(u1_struct_0(X0),X5,X1) != X4
      | r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f2403])).

fof(f2403,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2244])).

fof(f2244,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

fof(f4984,plain,
    ( ~ spl180_57
    | ~ spl180_5 ),
    inference(avatar_split_clause,[],[f4963,f4462,f4981])).

fof(f4981,plain,
    ( spl180_57
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_57])])).

fof(f4963,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl180_5 ),
    inference(resolution,[],[f3504,f4464])).

fof(f3504,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f2667])).

fof(f2667,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f4979,plain,
    ( spl180_56
    | ~ spl180_55
    | ~ spl180_2 ),
    inference(avatar_split_clause,[],[f4961,f4447,f4972,f4977])).

fof(f4977,plain,
    ( spl180_56
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_56])])).

fof(f4972,plain,
    ( spl180_55
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_55])])).

fof(f4447,plain,
    ( spl180_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_2])])).

fof(f4961,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl180_2 ),
    inference(resolution,[],[f3504,f4760])).

fof(f4760,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl180_2 ),
    inference(resolution,[],[f3224,f4449])).

fof(f4449,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl180_2 ),
    inference(avatar_component_clause,[],[f4447])).

fof(f3224,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f2439])).

fof(f2439,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f4975,plain,
    ( spl180_54
    | ~ spl180_55
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f4960,f4452,f4972,f4969])).

fof(f4969,plain,
    ( spl180_54
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_54])])).

fof(f4960,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl180_3 ),
    inference(resolution,[],[f3504,f4761])).

fof(f4761,plain,
    ( ! [X1] :
        ( r2_hidden(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl180_3 ),
    inference(resolution,[],[f3224,f4454])).

fof(f4940,plain,
    ( ~ spl180_53
    | ~ spl180_6 ),
    inference(avatar_split_clause,[],[f4935,f4467,f4937])).

fof(f4937,plain,
    ( spl180_53
  <=> r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_53])])).

fof(f4935,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK3)
    | ~ spl180_6 ),
    inference(duplicate_literal_removal,[],[f4934])).

fof(f4934,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK3)
    | ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK3)
    | ~ spl180_6 ),
    inference(resolution,[],[f4883,f4762])).

fof(f4762,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK3) )
    | ~ spl180_6 ),
    inference(resolution,[],[f3224,f4469])).

fof(f4883,plain,
    ( ! [X14] :
        ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),X14)
        | ~ r2_hidden(X14,sK3) )
    | ~ spl180_6 ),
    inference(resolution,[],[f4762,f3228])).

fof(f3228,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2443])).

fof(f2443,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f4914,plain,
    ( ~ spl180_51
    | ~ spl180_52
    | ~ spl180_5
    | ~ spl180_6 ),
    inference(avatar_split_clause,[],[f4888,f4467,f4462,f4911,f4906])).

fof(f4906,plain,
    ( spl180_51
  <=> r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_51])])).

fof(f4911,plain,
    ( spl180_52
  <=> r2_hidden(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_52])])).

fof(f4888,plain,
    ( ~ r2_hidden(sK3,sK3)
    | ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl180_5
    | ~ spl180_6 ),
    inference(resolution,[],[f4762,f4706])).

fof(f4706,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl180_5 ),
    inference(resolution,[],[f3212,f4464])).

fof(f3212,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2430])).

fof(f2430,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1111])).

fof(f1111,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).

fof(f4909,plain,
    ( ~ spl180_51
    | ~ spl180_50
    | ~ spl180_2
    | ~ spl180_6 ),
    inference(avatar_split_clause,[],[f4887,f4467,f4447,f4901,f4906])).

fof(f4901,plain,
    ( spl180_50
  <=> r2_hidden(u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_50])])).

fof(f4887,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3)
    | ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl180_2
    | ~ spl180_6 ),
    inference(resolution,[],[f4762,f4807])).

fof(f4807,plain,
    ( ! [X5] :
        ( ~ r2_hidden(u1_struct_0(sK0),X5)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl180_2 ),
    inference(resolution,[],[f4760,f3228])).

fof(f4904,plain,
    ( ~ spl180_49
    | ~ spl180_50
    | ~ spl180_3
    | ~ spl180_6 ),
    inference(avatar_split_clause,[],[f4886,f4467,f4452,f4901,f4897])).

fof(f4897,plain,
    ( spl180_49
  <=> r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_49])])).

fof(f4886,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3)
    | ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl180_3
    | ~ spl180_6 ),
    inference(resolution,[],[f4762,f4822])).

fof(f4822,plain,
    ( ! [X5] :
        ( ~ r2_hidden(u1_struct_0(sK0),X5)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl180_3 ),
    inference(resolution,[],[f4761,f3228])).

fof(f4895,plain,
    ( ~ spl180_48
    | ~ spl180_6 ),
    inference(avatar_split_clause,[],[f4885,f4467,f4892])).

fof(f4892,plain,
    ( spl180_48
  <=> r2_hidden(k1_tarski(k1_zfmisc_1(u1_struct_0(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_48])])).

fof(f4885,plain,
    ( ~ r2_hidden(k1_tarski(k1_zfmisc_1(u1_struct_0(sK0))),sK3)
    | ~ spl180_6 ),
    inference(resolution,[],[f4762,f4727])).

fof(f4727,plain,(
    ! [X2] : ~ r2_hidden(k1_tarski(X2),X2) ),
    inference(resolution,[],[f4363,f3228])).

fof(f4363,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f4362])).

fof(f4362,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f3624])).

fof(f3624,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f4862,plain,
    ( ~ spl180_47
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f4857,f4452,f4859])).

fof(f4859,plain,
    ( spl180_47
  <=> r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_47])])).

fof(f4857,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl180_3 ),
    inference(duplicate_literal_removal,[],[f4855])).

fof(f4855,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl180_3 ),
    inference(resolution,[],[f4822,f4761])).

fof(f4841,plain,
    ( ~ spl180_45
    | ~ spl180_46
    | ~ spl180_3
    | ~ spl180_5 ),
    inference(avatar_split_clause,[],[f4825,f4462,f4452,f4838,f4834])).

fof(f4834,plain,
    ( spl180_45
  <=> r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_45])])).

fof(f4838,plain,
    ( spl180_46
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_46])])).

fof(f4825,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl180_3
    | ~ spl180_5 ),
    inference(resolution,[],[f4761,f4706])).

fof(f4832,plain,
    ( ~ spl180_44
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f4824,f4452,f4829])).

fof(f4829,plain,
    ( spl180_44
  <=> r2_hidden(k1_tarski(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_44])])).

fof(f4824,plain,
    ( ~ r2_hidden(k1_tarski(u1_struct_0(sK0)),sK2)
    | ~ spl180_3 ),
    inference(resolution,[],[f4761,f4727])).

fof(f4816,plain,
    ( ~ spl180_43
    | ~ spl180_2 ),
    inference(avatar_split_clause,[],[f4809,f4447,f4813])).

fof(f4813,plain,
    ( spl180_43
  <=> r2_hidden(k1_tarski(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_43])])).

fof(f4809,plain,
    ( ~ r2_hidden(k1_tarski(u1_struct_0(sK0)),sK1)
    | ~ spl180_2 ),
    inference(resolution,[],[f4760,f4727])).

fof(f4784,plain,
    ( ~ spl180_42
    | ~ spl180_3
    | spl180_4 ),
    inference(avatar_split_clause,[],[f4779,f4457,f4452,f4781])).

fof(f4781,plain,
    ( spl180_42
  <=> r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_42])])).

fof(f4779,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    | ~ spl180_3
    | spl180_4 ),
    inference(subsumption_resolution,[],[f4775,f4454])).

fof(f4775,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl180_4 ),
    inference(superposition,[],[f4459,f3193])).

fof(f3193,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2407])).

fof(f2407,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f4770,plain,
    ( spl180_41
    | ~ spl180_29 ),
    inference(avatar_split_clause,[],[f4765,f4635,f4767])).

fof(f4767,plain,
    ( spl180_41
  <=> l1_struct_0(sK109) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_41])])).

fof(f4635,plain,
    ( spl180_29
  <=> l1_orders_2(sK109) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_29])])).

fof(f4765,plain,
    ( l1_struct_0(sK109)
    | ~ spl180_29 ),
    inference(resolution,[],[f3879,f4637])).

fof(f4637,plain,
    ( l1_orders_2(sK109)
    | ~ spl180_29 ),
    inference(avatar_component_clause,[],[f4635])).

fof(f3879,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2889])).

fof(f2889,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f4758,plain,
    ( spl180_40
    | ~ spl180_16 ),
    inference(avatar_split_clause,[],[f4738,f4531,f4755])).

fof(f4755,plain,
    ( spl180_40
  <=> l1_struct_0(sK47) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_40])])).

fof(f4531,plain,
    ( spl180_16
  <=> l1_pre_topc(sK47) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_16])])).

fof(f4738,plain,
    ( l1_struct_0(sK47)
    | ~ spl180_16 ),
    inference(resolution,[],[f3878,f4533])).

fof(f4533,plain,
    ( l1_pre_topc(sK47)
    | ~ spl180_16 ),
    inference(avatar_component_clause,[],[f4531])).

fof(f3878,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2888])).

fof(f2888,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4753,plain,
    ( spl180_39
    | ~ spl180_14 ),
    inference(avatar_split_clause,[],[f4737,f4521,f4750])).

fof(f4750,plain,
    ( spl180_39
  <=> l1_struct_0(sK46) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_39])])).

fof(f4521,plain,
    ( spl180_14
  <=> l1_pre_topc(sK46) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_14])])).

fof(f4737,plain,
    ( l1_struct_0(sK46)
    | ~ spl180_14 ),
    inference(resolution,[],[f3878,f4523])).

fof(f4523,plain,
    ( l1_pre_topc(sK46)
    | ~ spl180_14 ),
    inference(avatar_component_clause,[],[f4521])).

fof(f4748,plain,
    ( spl180_38
    | ~ spl180_7 ),
    inference(avatar_split_clause,[],[f4736,f4476,f4745])).

fof(f4745,plain,
    ( spl180_38
  <=> l1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_38])])).

fof(f4476,plain,
    ( spl180_7
  <=> l1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_7])])).

fof(f4736,plain,
    ( l1_struct_0(sK14)
    | ~ spl180_7 ),
    inference(resolution,[],[f3878,f4478])).

fof(f4478,plain,
    ( l1_pre_topc(sK14)
    | ~ spl180_7 ),
    inference(avatar_component_clause,[],[f4476])).

fof(f4743,plain,
    ( spl180_37
    | ~ spl180_1 ),
    inference(avatar_split_clause,[],[f4735,f4442,f4740])).

fof(f4740,plain,
    ( spl180_37
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_37])])).

fof(f4735,plain,
    ( l1_struct_0(sK0)
    | ~ spl180_1 ),
    inference(resolution,[],[f3878,f4444])).

fof(f4734,plain,
    ( ~ spl180_36
    | ~ spl180_5 ),
    inference(avatar_split_clause,[],[f4729,f4462,f4731])).

fof(f4731,plain,
    ( spl180_36
  <=> r2_hidden(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_36])])).

fof(f4729,plain,
    ( ~ r2_hidden(k1_tarski(sK3),sK1)
    | ~ spl180_5 ),
    inference(resolution,[],[f4363,f4706])).

fof(f4720,plain,
    ( spl180_35
    | ~ spl180_21 ),
    inference(avatar_split_clause,[],[f4709,f4556,f4717])).

fof(f4717,plain,
    ( spl180_35
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_35])])).

fof(f4556,plain,
    ( spl180_21
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_21])])).

fof(f4709,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl180_21 ),
    inference(resolution,[],[f3526,f4558])).

fof(f4558,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl180_21 ),
    inference(avatar_component_clause,[],[f4556])).

fof(f3526,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f2685])).

fof(f2685,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f4715,plain,
    ( spl180_34
    | ~ spl180_19 ),
    inference(avatar_split_clause,[],[f4708,f4546,f4712])).

fof(f4712,plain,
    ( spl180_34
  <=> v1_funct_1(sK52) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_34])])).

fof(f4546,plain,
    ( spl180_19
  <=> v1_xboole_0(sK52) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_19])])).

fof(f4708,plain,
    ( v1_funct_1(sK52)
    | ~ spl180_19 ),
    inference(resolution,[],[f3526,f4548])).

fof(f4548,plain,
    ( v1_xboole_0(sK52)
    | ~ spl180_19 ),
    inference(avatar_component_clause,[],[f4546])).

fof(f4705,plain,
    ( spl180_33
    | ~ spl180_21 ),
    inference(avatar_split_clause,[],[f4694,f4556,f4702])).

fof(f4702,plain,
    ( spl180_33
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_33])])).

fof(f4694,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl180_21 ),
    inference(resolution,[],[f3525,f4558])).

fof(f3525,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2684])).

fof(f2684,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f4700,plain,
    ( spl180_32
    | ~ spl180_19 ),
    inference(avatar_split_clause,[],[f4693,f4546,f4697])).

fof(f4697,plain,
    ( spl180_32
  <=> v1_relat_1(sK52) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_32])])).

fof(f4693,plain,
    ( v1_relat_1(sK52)
    | ~ spl180_19 ),
    inference(resolution,[],[f3525,f4548])).

fof(f4690,plain,
    ( ~ spl180_31
    | ~ spl180_5 ),
    inference(avatar_split_clause,[],[f4685,f4462,f4687])).

fof(f4687,plain,
    ( spl180_31
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_31])])).

fof(f4685,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl180_5 ),
    inference(resolution,[],[f3228,f4464])).

fof(f4684,plain,
    ( spl180_30
    | ~ spl180_5 ),
    inference(avatar_split_clause,[],[f4679,f4462,f4681])).

fof(f4681,plain,
    ( spl180_30
  <=> m1_subset_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_30])])).

fof(f4679,plain,
    ( m1_subset_1(sK1,sK3)
    | ~ spl180_5 ),
    inference(resolution,[],[f3227,f4464])).

fof(f3227,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2442])).

fof(f2442,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f4638,plain,(
    spl180_29 ),
    inference(avatar_split_clause,[],[f4077,f4635])).

fof(f4077,plain,(
    l1_orders_2(sK109) ),
    inference(cnf_transformation,[],[f1906])).

fof(f1906,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_orders_2)).

fof(f4633,plain,(
    spl180_28 ),
    inference(avatar_split_clause,[],[f4075,f4630])).

fof(f4630,plain,
    ( spl180_28
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_28])])).

fof(f4075,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f4628,plain,(
    spl180_27 ),
    inference(avatar_split_clause,[],[f4076,f4625])).

fof(f4625,plain,
    ( spl180_27
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_27])])).

fof(f4076,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f4616,plain,(
    spl180_26 ),
    inference(avatar_split_clause,[],[f3872,f4613])).

fof(f4613,plain,
    ( spl180_26
  <=> l1_struct_0(sK85) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_26])])).

fof(f3872,plain,(
    l1_struct_0(sK85) ),
    inference(cnf_transformation,[],[f1789])).

fof(f1789,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_struct_0)).

fof(f4601,plain,(
    spl180_25 ),
    inference(avatar_split_clause,[],[f4368,f4598])).

fof(f4598,plain,
    ( spl180_25
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_25])])).

fof(f4368,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f3778])).

fof(f3778,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2852])).

fof(f2852,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f4586,plain,(
    spl180_24 ),
    inference(avatar_split_clause,[],[f3677,f4583])).

fof(f4583,plain,
    ( spl180_24
  <=> v1_relat_1(sK66) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_24])])).

fof(f3677,plain,(
    v1_relat_1(sK66) ),
    inference(cnf_transformation,[],[f930])).

fof(f930,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_1)).

fof(f4581,plain,(
    spl180_23 ),
    inference(avatar_split_clause,[],[f3678,f4578])).

fof(f4578,plain,
    ( spl180_23
  <=> v1_funct_1(sK66) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_23])])).

fof(f3678,plain,(
    v1_funct_1(sK66) ),
    inference(cnf_transformation,[],[f930])).

fof(f4572,plain,(
    spl180_22 ),
    inference(avatar_split_clause,[],[f3642,f4569])).

fof(f4569,plain,
    ( spl180_22
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_22])])).

fof(f3642,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f4559,plain,(
    spl180_21 ),
    inference(avatar_split_clause,[],[f3533,f4556])).

fof(f3533,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4554,plain,(
    ~ spl180_20 ),
    inference(avatar_split_clause,[],[f3502,f4551])).

fof(f4551,plain,
    ( spl180_20
  <=> v1_xboole_0(sK53) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_20])])).

fof(f3502,plain,(
    ~ v1_xboole_0(sK53) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_xboole_0)).

fof(f4549,plain,(
    spl180_19 ),
    inference(avatar_split_clause,[],[f3501,f4546])).

fof(f3501,plain,(
    v1_xboole_0(sK52) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f4544,plain,(
    ~ spl180_18 ),
    inference(avatar_split_clause,[],[f3499,f4541])).

fof(f4541,plain,
    ( spl180_18
  <=> v1_xboole_0(sK51) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_18])])).

fof(f3499,plain,(
    ~ v1_xboole_0(sK51) ),
    inference(cnf_transformation,[],[f702])).

fof(f702,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f4539,plain,(
    spl180_17 ),
    inference(avatar_split_clause,[],[f3500,f4536])).

fof(f4536,plain,
    ( spl180_17
  <=> v1_relat_1(sK51) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_17])])).

fof(f3500,plain,(
    v1_relat_1(sK51) ),
    inference(cnf_transformation,[],[f702])).

fof(f4534,plain,(
    spl180_16 ),
    inference(avatar_split_clause,[],[f3480,f4531])).

fof(f3480,plain,(
    l1_pre_topc(sK47) ),
    inference(cnf_transformation,[],[f1812])).

fof(f1812,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_pre_topc)).

fof(f4529,plain,(
    spl180_15 ),
    inference(avatar_split_clause,[],[f3481,f4526])).

fof(f4526,plain,
    ( spl180_15
  <=> v1_pre_topc(sK47) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_15])])).

fof(f3481,plain,(
    v1_pre_topc(sK47) ),
    inference(cnf_transformation,[],[f1812])).

fof(f4524,plain,(
    spl180_14 ),
    inference(avatar_split_clause,[],[f3477,f4521])).

fof(f3477,plain,(
    l1_pre_topc(sK46) ),
    inference(cnf_transformation,[],[f2305])).

fof(f2305,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc11_pre_topc)).

fof(f4519,plain,(
    spl180_13 ),
    inference(avatar_split_clause,[],[f3478,f4516])).

fof(f4516,plain,
    ( spl180_13
  <=> v2_struct_0(sK46) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_13])])).

fof(f3478,plain,(
    v2_struct_0(sK46) ),
    inference(cnf_transformation,[],[f2305])).

fof(f4514,plain,(
    spl180_12 ),
    inference(avatar_split_clause,[],[f3479,f4511])).

fof(f4511,plain,
    ( spl180_12
  <=> v1_pre_topc(sK46) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_12])])).

fof(f3479,plain,(
    v1_pre_topc(sK46) ),
    inference(cnf_transformation,[],[f2305])).

fof(f4507,plain,
    ( spl180_10
    | spl180_11 ),
    inference(avatar_split_clause,[],[f3431,f4505,f4502])).

fof(f4502,plain,
    ( spl180_10
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_10])])).

fof(f4505,plain,
    ( spl180_11
  <=> ! [X0,X2] :
        ( ~ v2_pre_topc(X0)
        | v3_pre_topc(X2,X0)
        | k1_tops_1(X0,X2) != X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_11])])).

fof(f3431,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f2600])).

fof(f2600,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2599])).

fof(f2599,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2166])).

fof(f2166,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f4500,plain,
    ( spl180_8
    | spl180_9 ),
    inference(avatar_split_clause,[],[f3432,f4498,f4495])).

fof(f4495,plain,
    ( spl180_8
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_8])])).

fof(f4498,plain,
    ( spl180_9
  <=> ! [X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_9])])).

fof(f3432,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f2600])).

fof(f4479,plain,(
    spl180_7 ),
    inference(avatar_split_clause,[],[f3231,f4476])).

fof(f3231,plain,(
    l1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f1788])).

fof(f1788,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_pre_topc)).

fof(f4470,plain,(
    spl180_6 ),
    inference(avatar_split_clause,[],[f3175,f4467])).

fof(f3175,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f2400])).

fof(f2400,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2399])).

fof(f2399,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2381])).

fof(f2381,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2380])).

fof(f2380,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

fof(f4465,plain,(
    spl180_5 ),
    inference(avatar_split_clause,[],[f3176,f4462])).

fof(f3176,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f2400])).

fof(f4460,plain,(
    ~ spl180_4 ),
    inference(avatar_split_clause,[],[f3177,f4457])).

fof(f3177,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f2400])).

fof(f4455,plain,(
    spl180_3 ),
    inference(avatar_split_clause,[],[f3178,f4452])).

fof(f3178,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2400])).

fof(f4450,plain,(
    spl180_2 ),
    inference(avatar_split_clause,[],[f3179,f4447])).

fof(f3179,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2400])).

fof(f4445,plain,(
    spl180_1 ),
    inference(avatar_split_clause,[],[f3180,f4442])).

fof(f3180,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2400])).
%------------------------------------------------------------------------------
