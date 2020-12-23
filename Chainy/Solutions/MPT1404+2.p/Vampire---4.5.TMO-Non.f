%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1404+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:20 EST 2020

% Result     : Timeout 57.87s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  161 ( 457 expanded)
%              Number of leaves         :   38 ( 196 expanded)
%              Depth                    :   14
%              Number of atoms          :  951 (2861 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4207,f4212,f4217,f4222,f4227,f4251,f4256,f4265,f6365,f23146,f23204,f23504,f88285,f91995,f93692,f94465,f94991,f97087,f113187,f114207])).

fof(f114207,plain,
    ( ~ spl137_3
    | ~ spl137_5
    | ~ spl137_9
    | ~ spl137_338
    | ~ spl137_340
    | ~ spl137_346
    | ~ spl137_432 ),
    inference(avatar_contradiction_clause,[],[f114206])).

fof(f114206,plain,
    ( $false
    | ~ spl137_3
    | ~ spl137_5
    | ~ spl137_9
    | ~ spl137_338
    | ~ spl137_340
    | ~ spl137_346
    | ~ spl137_432 ),
    inference(subsumption_resolution,[],[f113214,f97500])).

fof(f97500,plain,
    ( ~ r1_xboole_0(sK1,sK21(sK0,sK2,sK3))
    | ~ spl137_3
    | ~ spl137_5
    | ~ spl137_9
    | ~ spl137_338
    | ~ spl137_340
    | ~ spl137_346 ),
    inference(unit_resulting_resolution,[],[f4216,f4226,f4245,f93691,f94990,f97086,f4174])).

fof(f4174,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X1,X8) ) ),
    inference(subsumption_resolution,[],[f4173,f3460])).

fof(f3460,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2680])).

fof(f2680,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2679])).

fof(f2679,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f4173,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f4029,f3453])).

fof(f3453,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f2670])).

fof(f2670,plain,(
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

fof(f4029,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3468])).

fof(f3468,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3136,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ( ( ( r1_xboole_0(X1,sK29(X0,X1,X2))
                        & r2_hidden(sK28(X0,X1,X2),sK29(X0,X1,X2))
                        & v3_pre_topc(sK29(X0,X1,X2),X0)
                        & m1_subset_1(sK29(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ r2_hidden(sK28(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( ~ r1_xboole_0(X1,X5)
                          | ~ r2_hidden(sK28(X0,X1,X2),X5)
                          | ~ v3_pre_topc(X5,X0)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                      | r2_hidden(sK28(X0,X1,X2),X2) )
                    & r2_hidden(sK28(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( r1_xboole_0(X1,sK30(X0,X1,X6))
                            & r2_hidden(X6,sK30(X0,X1,X6))
                            & v3_pre_topc(sK30(X0,X1,X6),X0)
                            & m1_subset_1(sK30(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f3132,f3135,f3134,f3133])).

fof(f3133,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X1,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X1,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X0)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X1,X4)
              & r2_hidden(sK28(X0,X1,X2),X4)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK28(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X1,X5)
              | ~ r2_hidden(sK28(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK28(X0,X1,X2),X2) )
        & r2_hidden(sK28(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3134,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X1,X4)
          & r2_hidden(sK28(X0,X1,X2),X4)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK29(X0,X1,X2))
        & r2_hidden(sK28(X0,X1,X2),sK29(X0,X1,X2))
        & v3_pre_topc(sK29(X0,X1,X2),X0)
        & m1_subset_1(sK29(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3135,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X1,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK30(X0,X1,X6))
        & r2_hidden(X6,sK30(X0,X1,X6))
        & v3_pre_topc(sK30(X0,X1,X6),X0)
        & m1_subset_1(sK30(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3132,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( ~ r1_xboole_0(X1,X5)
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( r1_xboole_0(X1,X7)
                              & r2_hidden(X6,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f3131])).

fof(f3131,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3130])).

fof(f3130,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2688])).

fof(f2688,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2687])).

fof(f2687,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1770])).

fof(f1770,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).

fof(f97086,plain,
    ( m1_subset_1(sK21(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl137_346 ),
    inference(avatar_component_clause,[],[f97084])).

fof(f97084,plain,
    ( spl137_346
  <=> m1_subset_1(sK21(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_346])])).

fof(f94990,plain,
    ( v3_pre_topc(sK21(sK0,sK2,sK3),sK0)
    | ~ spl137_340 ),
    inference(avatar_component_clause,[],[f94988])).

fof(f94988,plain,
    ( spl137_340
  <=> v3_pre_topc(sK21(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_340])])).

fof(f93691,plain,
    ( r2_hidden(sK2,sK21(sK0,sK2,sK3))
    | ~ spl137_338 ),
    inference(avatar_component_clause,[],[f93689])).

fof(f93689,plain,
    ( spl137_338
  <=> r2_hidden(sK2,sK21(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_338])])).

fof(f4245,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl137_9 ),
    inference(avatar_component_clause,[],[f4244])).

fof(f4244,plain,
    ( spl137_9
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_9])])).

fof(f4226,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl137_5 ),
    inference(avatar_component_clause,[],[f4224])).

fof(f4224,plain,
    ( spl137_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_5])])).

fof(f4216,plain,
    ( l1_pre_topc(sK0)
    | ~ spl137_3 ),
    inference(avatar_component_clause,[],[f4214])).

fof(f4214,plain,
    ( spl137_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_3])])).

fof(f113214,plain,
    ( r1_xboole_0(sK1,sK21(sK0,sK2,sK3))
    | ~ spl137_432 ),
    inference(unit_resulting_resolution,[],[f113186,f3374])).

fof(f3374,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f2609])).

fof(f2609,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f113186,plain,
    ( r1_xboole_0(sK21(sK0,sK2,sK3),sK1)
    | ~ spl137_432 ),
    inference(avatar_component_clause,[],[f113184])).

fof(f113184,plain,
    ( spl137_432
  <=> r1_xboole_0(sK21(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_432])])).

fof(f113187,plain,
    ( spl137_432
    | ~ spl137_10
    | ~ spl137_339 ),
    inference(avatar_split_clause,[],[f94466,f94462,f4248,f113184])).

fof(f4248,plain,
    ( spl137_10
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_10])])).

fof(f94462,plain,
    ( spl137_339
  <=> r1_tarski(sK21(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_339])])).

fof(f94466,plain,
    ( r1_xboole_0(sK21(sK0,sK2,sK3),sK1)
    | ~ spl137_10
    | ~ spl137_339 ),
    inference(unit_resulting_resolution,[],[f4250,f94464,f3361])).

fof(f3361,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f2599])).

fof(f2599,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2598])).

fof(f2598,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f129])).

fof(f129,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f94464,plain,
    ( r1_tarski(sK21(sK0,sK2,sK3),sK3)
    | ~ spl137_339 ),
    inference(avatar_component_clause,[],[f94462])).

fof(f4250,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl137_10 ),
    inference(avatar_component_clause,[],[f4248])).

fof(f97087,plain,
    ( spl137_346
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(avatar_split_clause,[],[f92043,f4253,f4219,f4214,f4209,f4204,f97084])).

fof(f4204,plain,
    ( spl137_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_1])])).

fof(f4209,plain,
    ( spl137_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_2])])).

fof(f4219,plain,
    ( spl137_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_4])])).

fof(f4253,plain,
    ( spl137_11
  <=> m1_connsp_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_11])])).

fof(f92043,plain,
    ( m1_subset_1(sK21(sK0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(unit_resulting_resolution,[],[f4206,f4211,f4216,f4221,f4255,f4166])).

fof(f4166,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(sK21(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3431,f3411])).

fof(f3411,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2637])).

fof(f2637,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2636])).

fof(f2636,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2529])).

fof(f2529,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f3431,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK21(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f3109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK21(X0,X1,X2))
                    & r1_tarski(sK21(X0,X1,X2),X2)
                    & v3_pre_topc(sK21(X0,X1,X2),X0)
                    & m1_subset_1(sK21(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f3107,f3108])).

fof(f3108,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK21(X0,X1,X2))
        & r1_tarski(sK21(X0,X1,X2),X2)
        & v3_pre_topc(sK21(X0,X1,X2),X0)
        & m1_subset_1(sK21(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3106])).

fof(f3106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2655])).

fof(f2655,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2654])).

fof(f2654,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2567])).

fof(f2567,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f4255,plain,
    ( m1_connsp_2(sK3,sK0,sK2)
    | ~ spl137_11 ),
    inference(avatar_component_clause,[],[f4253])).

fof(f4221,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl137_4 ),
    inference(avatar_component_clause,[],[f4219])).

fof(f4211,plain,
    ( v2_pre_topc(sK0)
    | ~ spl137_2 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f4206,plain,
    ( ~ v2_struct_0(sK0)
    | spl137_1 ),
    inference(avatar_component_clause,[],[f4204])).

fof(f94991,plain,
    ( spl137_340
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(avatar_split_clause,[],[f92042,f4253,f4219,f4214,f4209,f4204,f94988])).

fof(f92042,plain,
    ( v3_pre_topc(sK21(sK0,sK2,sK3),sK0)
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(unit_resulting_resolution,[],[f4206,f4211,f4216,f4221,f4255,f4165])).

fof(f4165,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK21(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3432,f3411])).

fof(f3432,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK21(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f94465,plain,
    ( spl137_339
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(avatar_split_clause,[],[f92041,f4253,f4219,f4214,f4209,f4204,f94462])).

fof(f92041,plain,
    ( r1_tarski(sK21(sK0,sK2,sK3),sK3)
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(unit_resulting_resolution,[],[f4206,f4211,f4216,f4221,f4255,f4164])).

fof(f4164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | r1_tarski(sK21(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3433,f3411])).

fof(f3433,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK21(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f93692,plain,
    ( spl137_338
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(avatar_split_clause,[],[f92040,f4253,f4219,f4214,f4209,f4204,f93689])).

fof(f92040,plain,
    ( r2_hidden(sK2,sK21(sK0,sK2,sK3))
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_11 ),
    inference(unit_resulting_resolution,[],[f4206,f4211,f4216,f4221,f4255,f4163])).

fof(f4163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,sK21(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f3434,f3411])).

fof(f3434,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK21(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f91995,plain,
    ( spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_13
    | ~ spl137_54
    | ~ spl137_110
    | ~ spl137_119
    | ~ spl137_311 ),
    inference(avatar_contradiction_clause,[],[f91994])).

fof(f91994,plain,
    ( $false
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_13
    | ~ spl137_54
    | ~ spl137_110
    | ~ spl137_119
    | ~ spl137_311 ),
    inference(subsumption_resolution,[],[f91408,f23609])).

fof(f23609,plain,
    ( m1_connsp_2(sK31(sK0,sK1,sK2),sK0,sK2)
    | spl137_1
    | ~ spl137_2
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_54
    | ~ spl137_110
    | ~ spl137_119 ),
    inference(unit_resulting_resolution,[],[f4206,f4211,f4216,f4221,f23503,f4035,f23145,f6364,f23503,f3435])).

fof(f3435,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X2,X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f6364,plain,
    ( v3_pre_topc(sK31(sK0,sK1,sK2),sK0)
    | ~ spl137_54 ),
    inference(avatar_component_clause,[],[f6362])).

fof(f6362,plain,
    ( spl137_54
  <=> v3_pre_topc(sK31(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_54])])).

fof(f23145,plain,
    ( r2_hidden(sK2,sK31(sK0,sK1,sK2))
    | ~ spl137_110 ),
    inference(avatar_component_clause,[],[f23143])).

fof(f23143,plain,
    ( spl137_110
  <=> r2_hidden(sK2,sK31(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_110])])).

fof(f4035,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f3570])).

fof(f3570,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3167])).

fof(f3167,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3166])).

fof(f3166,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f23503,plain,
    ( m1_subset_1(sK31(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl137_119 ),
    inference(avatar_component_clause,[],[f23501])).

fof(f23501,plain,
    ( spl137_119
  <=> m1_subset_1(sK31(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_119])])).

fof(f91408,plain,
    ( ~ m1_connsp_2(sK31(sK0,sK1,sK2),sK0,sK2)
    | ~ spl137_13
    | ~ spl137_311 ),
    inference(unit_resulting_resolution,[],[f88284,f4264])).

fof(f4264,plain,
    ( ! [X4] :
        ( ~ m1_connsp_2(X4,sK0,sK2)
        | ~ r1_xboole_0(X4,sK1) )
    | ~ spl137_13 ),
    inference(avatar_component_clause,[],[f4263])).

fof(f4263,plain,
    ( spl137_13
  <=> ! [X4] :
        ( ~ r1_xboole_0(X4,sK1)
        | ~ m1_connsp_2(X4,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_13])])).

fof(f88284,plain,
    ( r1_xboole_0(sK31(sK0,sK1,sK2),sK1)
    | ~ spl137_311 ),
    inference(avatar_component_clause,[],[f88282])).

fof(f88282,plain,
    ( spl137_311
  <=> r1_xboole_0(sK31(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_311])])).

fof(f88285,plain,
    ( spl137_311
    | ~ spl137_112 ),
    inference(avatar_split_clause,[],[f23231,f23201,f88282])).

fof(f23201,plain,
    ( spl137_112
  <=> r1_xboole_0(sK1,sK31(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl137_112])])).

fof(f23231,plain,
    ( r1_xboole_0(sK31(sK0,sK1,sK2),sK1)
    | ~ spl137_112 ),
    inference(unit_resulting_resolution,[],[f23203,f3374])).

fof(f23203,plain,
    ( r1_xboole_0(sK1,sK31(sK0,sK1,sK2))
    | ~ spl137_112 ),
    inference(avatar_component_clause,[],[f23201])).

fof(f23504,plain,
    ( spl137_119
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(avatar_split_clause,[],[f23087,f4244,f4224,f4219,f4214,f4204,f23501])).

fof(f23087,plain,
    ( m1_subset_1(sK31(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(unit_resulting_resolution,[],[f4216,f4206,f4221,f4226,f4246,f3485])).

fof(f3485,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK31(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3141])).

fof(f3141,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK31(X0,X1,X2))
                    & r2_hidden(X2,sK31(X0,X1,X2))
                    & v3_pre_topc(sK31(X0,X1,X2),X0)
                    & m1_subset_1(sK31(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31])],[f3139,f3140])).

fof(f3140,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK31(X0,X1,X2))
        & r2_hidden(X2,sK31(X0,X1,X2))
        & v3_pre_topc(sK31(X0,X1,X2),X0)
        & m1_subset_1(sK31(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3139,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f3138])).

fof(f3138,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3137])).

fof(f3137,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2697])).

fof(f2697,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2696])).

fof(f2696,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1845])).

fof(f1845,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f4246,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl137_9 ),
    inference(avatar_component_clause,[],[f4244])).

fof(f23204,plain,
    ( spl137_112
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(avatar_split_clause,[],[f23090,f4244,f4224,f4219,f4214,f4204,f23201])).

fof(f23090,plain,
    ( r1_xboole_0(sK1,sK31(sK0,sK1,sK2))
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(unit_resulting_resolution,[],[f4216,f4206,f4221,f4226,f4246,f3488])).

fof(f3488,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_xboole_0(X1,sK31(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3141])).

fof(f23146,plain,
    ( spl137_110
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(avatar_split_clause,[],[f23089,f4244,f4224,f4219,f4214,f4204,f23143])).

fof(f23089,plain,
    ( r2_hidden(sK2,sK31(sK0,sK1,sK2))
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(unit_resulting_resolution,[],[f4216,f4206,f4221,f4226,f4246,f3487])).

fof(f3487,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(X2,sK31(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3141])).

fof(f6365,plain,
    ( spl137_54
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(avatar_split_clause,[],[f5479,f4244,f4224,f4219,f4214,f4204,f6362])).

fof(f5479,plain,
    ( v3_pre_topc(sK31(sK0,sK1,sK2),sK0)
    | spl137_1
    | ~ spl137_3
    | ~ spl137_4
    | ~ spl137_5
    | spl137_9 ),
    inference(unit_resulting_resolution,[],[f4216,f4206,f4221,f4226,f4246,f3486])).

fof(f3486,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK31(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3141])).

fof(f4265,plain,
    ( spl137_9
    | spl137_13 ),
    inference(avatar_split_clause,[],[f3341,f4263,f4244])).

fof(f3341,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,sK1)
      | ~ m1_connsp_2(X4,sK0,sK2)
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3072,plain,
    ( ( ( r1_xboole_0(sK3,sK1)
        & m1_connsp_2(sK3,sK0,sK2) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(X4,sK1)
          | ~ m1_connsp_2(X4,sK0,sK2) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3067,f3071,f3070,f3069,f3068])).

fof(f3068,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,sK0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,sK0,X2) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3069,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X3,X1)
                  & m1_connsp_2(X3,sK0,X2) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X4,X1)
                  | ~ m1_connsp_2(X4,sK0,X2) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X3,sK1)
                & m1_connsp_2(X3,sK0,X2) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(X4,sK1)
                | ~ m1_connsp_2(X4,sK0,X2) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3070,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( r1_xboole_0(X3,sK1)
              & m1_connsp_2(X3,sK0,X2) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X4,sK1)
              | ~ m1_connsp_2(X4,sK0,X2) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ? [X3] :
            ( r1_xboole_0(X3,sK1)
            & m1_connsp_2(X3,sK0,sK2) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(X4,sK1)
            | ~ m1_connsp_2(X4,sK0,sK2) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3071,plain,
    ( ? [X3] :
        ( r1_xboole_0(X3,sK1)
        & m1_connsp_2(X3,sK0,sK2) )
   => ( r1_xboole_0(sK3,sK1)
      & m1_connsp_2(sK3,sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3067,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f3066])).

fof(f3066,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3065])).

fof(f3065,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2578])).

fof(f2578,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2577])).

fof(f2577,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2558])).

fof(f2558,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_connsp_2(X3,X0,X2)
                     => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2557])).

fof(f2557,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_connsp_2)).

fof(f4256,plain,
    ( ~ spl137_9
    | spl137_11 ),
    inference(avatar_split_clause,[],[f3342,f4253,f4244])).

fof(f3342,plain,
    ( m1_connsp_2(sK3,sK0,sK2)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f3072])).

fof(f4251,plain,
    ( ~ spl137_9
    | spl137_10 ),
    inference(avatar_split_clause,[],[f3343,f4248,f4244])).

fof(f3343,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f3072])).

fof(f4227,plain,(
    spl137_5 ),
    inference(avatar_split_clause,[],[f3339,f4224])).

fof(f3339,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3072])).

fof(f4222,plain,(
    spl137_4 ),
    inference(avatar_split_clause,[],[f3340,f4219])).

fof(f3340,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3072])).

fof(f4217,plain,(
    spl137_3 ),
    inference(avatar_split_clause,[],[f3338,f4214])).

fof(f3338,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3072])).

fof(f4212,plain,(
    spl137_2 ),
    inference(avatar_split_clause,[],[f3337,f4209])).

fof(f3337,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3072])).

fof(f4207,plain,(
    ~ spl137_1 ),
    inference(avatar_split_clause,[],[f3336,f4204])).

fof(f3336,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3072])).
%------------------------------------------------------------------------------
