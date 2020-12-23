%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1756+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 17.83s
% Output     : Refutation 17.83s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 244 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :    7
%              Number of atoms          :  455 (2391 expanded)
%              Number of equality atoms :   10 ( 104 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4615,f4620,f4625,f4630,f4635,f4640,f4645,f4650,f4655,f4660,f4665,f4670,f4675,f4680,f4685,f4690,f4695,f4704,f4705,f4822,f6885,f6889,f7465,f8557])).

fof(f8557,plain,
    ( ~ spl101_15
    | ~ spl101_13
    | ~ spl101_34
    | spl101_408 ),
    inference(avatar_split_clause,[],[f8556,f7462,f4820,f4672,f4682])).

fof(f4682,plain,
    ( spl101_15
  <=> r2_hidden(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_15])])).

fof(f4672,plain,
    ( spl101_13
  <=> m1_subset_1(sK6,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_13])])).

fof(f4820,plain,
    ( spl101_34
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK1))
        | m1_connsp_2(sK4,sK1,X5)
        | ~ r2_hidden(X5,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_34])])).

fof(f7462,plain,
    ( spl101_408
  <=> m1_connsp_2(sK4,sK1,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_408])])).

fof(f8556,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK1))
    | ~ r2_hidden(sK6,sK4)
    | ~ spl101_34
    | spl101_408 ),
    inference(resolution,[],[f7464,f4821])).

fof(f4821,plain,
    ( ! [X5] :
        ( m1_connsp_2(sK4,sK1,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r2_hidden(X5,sK4) )
    | ~ spl101_34 ),
    inference(avatar_component_clause,[],[f4820])).

fof(f7464,plain,
    ( ~ m1_connsp_2(sK4,sK1,sK6)
    | spl101_408 ),
    inference(avatar_component_clause,[],[f7462])).

fof(f7465,plain,
    ( ~ spl101_14
    | ~ spl101_408
    | ~ spl101_12
    | ~ spl101_353 ),
    inference(avatar_split_clause,[],[f7397,f6883,f4667,f7462,f4677])).

fof(f4677,plain,
    ( spl101_14
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_14])])).

fof(f4667,plain,
    ( spl101_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_12])])).

fof(f6883,plain,
    ( spl101_353
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X0,sK1,sK6)
        | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_353])])).

fof(f7397,plain,
    ( ~ m1_connsp_2(sK4,sK1,sK6)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl101_12
    | ~ spl101_353 ),
    inference(resolution,[],[f6884,f4669])).

fof(f4669,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl101_12 ),
    inference(avatar_component_clause,[],[f4667])).

fof(f6884,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X0,sK1,sK6)
        | ~ r1_tarski(X0,u1_struct_0(sK3)) )
    | ~ spl101_353 ),
    inference(avatar_component_clause,[],[f6883])).

fof(f6889,plain,
    ( ~ spl101_18
    | spl101_3
    | ~ spl101_17
    | ~ spl101_13
    | spl101_353
    | ~ spl101_10
    | spl101_11
    | ~ spl101_7
    | ~ spl101_8
    | ~ spl101_9
    | ~ spl101_4
    | ~ spl101_5
    | spl101_6
    | ~ spl101_1
    | ~ spl101_2
    | spl101_19 ),
    inference(avatar_split_clause,[],[f6887,f4701,f4617,f4612,f4637,f4632,f4627,f4652,f4647,f4642,f4662,f4657,f6883,f4672,f4692,f4622,f4697])).

fof(f4697,plain,
    ( spl101_18
  <=> r1_tmap_1(sK1,sK0,sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_18])])).

fof(f4622,plain,
    ( spl101_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_3])])).

fof(f4692,plain,
    ( spl101_17
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_17])])).

fof(f4657,plain,
    ( spl101_10
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_10])])).

fof(f4662,plain,
    ( spl101_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_11])])).

fof(f4642,plain,
    ( spl101_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_7])])).

fof(f4647,plain,
    ( spl101_8
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_8])])).

fof(f4652,plain,
    ( spl101_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_9])])).

fof(f4627,plain,
    ( spl101_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_4])])).

fof(f4632,plain,
    ( spl101_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_5])])).

fof(f4637,plain,
    ( spl101_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_6])])).

fof(f4612,plain,
    ( spl101_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_1])])).

fof(f4617,plain,
    ( spl101_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_2])])).

fof(f4701,plain,
    ( spl101_19
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_19])])).

fof(f6887,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK1))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK6)
        | v2_struct_0(sK0)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK6) )
    | spl101_19 ),
    inference(resolution,[],[f4703,f4473])).

fof(f4473,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | v2_struct_0(X0)
      | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f3864])).

fof(f3864,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f3439])).

fof(f3439,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3438])).

fof(f3438,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3412])).

fof(f3412,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f4703,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | spl101_19 ),
    inference(avatar_component_clause,[],[f4701])).

fof(f6885,plain,
    ( spl101_18
    | spl101_3
    | ~ spl101_17
    | ~ spl101_13
    | spl101_353
    | ~ spl101_10
    | spl101_11
    | ~ spl101_7
    | ~ spl101_8
    | ~ spl101_9
    | ~ spl101_4
    | ~ spl101_5
    | spl101_6
    | ~ spl101_1
    | ~ spl101_2
    | ~ spl101_19 ),
    inference(avatar_split_clause,[],[f5117,f4701,f4617,f4612,f4637,f4632,f4627,f4652,f4647,f4642,f4662,f4657,f6883,f4672,f4692,f4622,f4697])).

fof(f5117,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK1))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK6)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK6) )
    | ~ spl101_19 ),
    inference(resolution,[],[f4702,f4474])).

fof(f4474,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f3863])).

fof(f3863,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f3439])).

fof(f4702,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ spl101_19 ),
    inference(avatar_component_clause,[],[f4701])).

fof(f4822,plain,
    ( ~ spl101_16
    | spl101_34
    | spl101_6
    | ~ spl101_4
    | ~ spl101_5
    | ~ spl101_12 ),
    inference(avatar_split_clause,[],[f4789,f4667,f4632,f4627,f4637,f4820,f4687])).

fof(f4687,plain,
    ( spl101_16
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_16])])).

fof(f4789,plain,
    ( ! [X5] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ v3_pre_topc(sK4,sK1)
        | ~ r2_hidden(X5,sK4)
        | m1_connsp_2(sK4,sK1,X5) )
    | ~ spl101_12 ),
    inference(resolution,[],[f4669,f4017])).

fof(f4017,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f3566])).

fof(f3566,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3565])).

fof(f3565,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2565])).

fof(f2565,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f4705,plain,
    ( spl101_18
    | spl101_19 ),
    inference(avatar_split_clause,[],[f4472,f4701,f4697])).

fof(f4472,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK6) ),
    inference(definition_unfolding,[],[f3840,f3846])).

fof(f3846,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f3435])).

fof(f3435,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3434])).

fof(f3434,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3414])).

fof(f3414,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ( ( X5 = X6
                                    & r1_tarski(X4,u1_struct_0(X3))
                                    & r2_hidden(X5,X4)
                                    & v3_pre_topc(X4,X1) )
                                 => ( r1_tmap_1(X1,X0,X2,X5)
                                  <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3413])).

fof(f3413,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f3840,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4704,plain,
    ( ~ spl101_18
    | ~ spl101_19 ),
    inference(avatar_split_clause,[],[f4471,f4701,f4697])).

fof(f4471,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK6) ),
    inference(definition_unfolding,[],[f3841,f3846])).

fof(f3841,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4695,plain,(
    spl101_17 ),
    inference(avatar_split_clause,[],[f3842,f4692])).

fof(f3842,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4690,plain,(
    spl101_16 ),
    inference(avatar_split_clause,[],[f3843,f4687])).

fof(f3843,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4685,plain,(
    spl101_15 ),
    inference(avatar_split_clause,[],[f4470,f4682])).

fof(f4470,plain,(
    r2_hidden(sK6,sK4) ),
    inference(definition_unfolding,[],[f3844,f3846])).

fof(f3844,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4680,plain,(
    spl101_14 ),
    inference(avatar_split_clause,[],[f3845,f4677])).

fof(f3845,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4675,plain,(
    spl101_13 ),
    inference(avatar_split_clause,[],[f4469,f4672])).

fof(f4469,plain,(
    m1_subset_1(sK6,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f3847,f3846])).

fof(f3847,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4670,plain,(
    spl101_12 ),
    inference(avatar_split_clause,[],[f3848,f4667])).

fof(f3848,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4665,plain,(
    ~ spl101_11 ),
    inference(avatar_split_clause,[],[f3849,f4662])).

fof(f3849,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4660,plain,(
    spl101_10 ),
    inference(avatar_split_clause,[],[f3850,f4657])).

fof(f3850,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4655,plain,(
    spl101_9 ),
    inference(avatar_split_clause,[],[f3851,f4652])).

fof(f3851,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4650,plain,(
    spl101_8 ),
    inference(avatar_split_clause,[],[f3852,f4647])).

fof(f3852,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4645,plain,(
    spl101_7 ),
    inference(avatar_split_clause,[],[f3853,f4642])).

fof(f3853,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4640,plain,(
    ~ spl101_6 ),
    inference(avatar_split_clause,[],[f3854,f4637])).

fof(f3854,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4635,plain,(
    spl101_5 ),
    inference(avatar_split_clause,[],[f3855,f4632])).

fof(f3855,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4630,plain,(
    spl101_4 ),
    inference(avatar_split_clause,[],[f3856,f4627])).

fof(f3856,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4625,plain,(
    ~ spl101_3 ),
    inference(avatar_split_clause,[],[f3857,f4622])).

fof(f3857,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4620,plain,(
    spl101_2 ),
    inference(avatar_split_clause,[],[f3858,f4617])).

fof(f3858,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3435])).

fof(f4615,plain,(
    spl101_1 ),
    inference(avatar_split_clause,[],[f3859,f4612])).

fof(f3859,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3435])).
%------------------------------------------------------------------------------
