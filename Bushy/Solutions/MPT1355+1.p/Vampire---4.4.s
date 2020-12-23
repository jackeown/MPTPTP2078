%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t10_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:49 EDT 2019

% Result     : Theorem 18.80s
% Output     : Refutation 18.80s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 432 expanded)
%              Number of leaves         :   29 ( 137 expanded)
%              Depth                    :   23
%              Number of atoms          :  767 (3667 expanded)
%              Number of equality atoms :    3 (  21 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f119,f126,f133,f140,f147,f156,f163,f6258,f6260])).

fof(f6260,plain,
    ( ~ spl9_5
    | ~ spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f6259,f116,f110,f121])).

fof(f121,plain,
    ( spl9_5
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f110,plain,
    ( spl9_1
  <=> ~ v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f116,plain,
    ( spl9_3
  <=> ~ v2_compts_1(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f6259,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f117,f5644])).

fof(f5644,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f75,f266,f5643])).

fof(f5643,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(sK3(X0,k2_struct_0(X0)),k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f5642,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',d3_struct_0)).

fof(f5642,plain,(
    ! [X1] :
      ( ~ m1_setfam_1(sK3(X1,k2_struct_0(X1)),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v1_compts_1(X1)
      | v2_compts_1(k2_struct_0(X1),X1) ) ),
    inference(global_subsumption,[],[f74,f75,f5640])).

fof(f5640,plain,(
    ! [X1] :
      ( v2_compts_1(k2_struct_0(X1),X1)
      | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_compts_1(X1)
      | ~ m1_setfam_1(sK3(X1,k2_struct_0(X1)),u1_struct_0(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f5631])).

fof(f5631,plain,(
    ! [X1] :
      ( v2_compts_1(k2_struct_0(X1),X1)
      | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_compts_1(X1)
      | ~ m1_setfam_1(sK3(X1,k2_struct_0(X1)),u1_struct_0(X1))
      | ~ m1_setfam_1(sK3(X1,k2_struct_0(X1)),u1_struct_0(X1))
      | ~ v1_compts_1(X1)
      | ~ l1_pre_topc(X1)
      | v2_compts_1(k2_struct_0(X1),X1)
      | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f5629,f1168])).

fof(f1168,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(sK2(X0,sK3(X0,X1)),k2_struct_0(X0))
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f789,f73])).

fof(f789,plain,(
    ! [X4,X3] :
      ( m1_setfam_1(sK2(X3,sK3(X3,X4)),u1_struct_0(X3))
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(global_subsumption,[],[f90,f787])).

fof(f787,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK3(X3,X4),X3)
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | m1_setfam_1(sK2(X3,sK3(X3,X4)),u1_struct_0(X3))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(duplicate_literal_removal,[],[f781])).

fof(f781,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK3(X3,X4),X3)
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | m1_setfam_1(sK2(X3,sK3(X3,X4)),u1_struct_0(X3))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f78,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ( ! [X3] :
                    ( ~ v1_finset_1(X3)
                    | ~ m1_setfam_1(X3,X1)
                    | ~ r1_tarski(X3,sK3(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & v1_tops_2(sK3(X0,X1),X0)
                & m1_setfam_1(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ( v1_finset_1(sK4(X0,X1,X4))
                    & m1_setfam_1(sK4(X0,X1,X4),X1)
                    & r1_tarski(sK4(X0,X1,X4),X4)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X1)
              | ~ r1_tarski(X3,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X2,X0)
          & m1_setfam_1(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X3] :
            ( ~ v1_finset_1(X3)
            | ~ m1_setfam_1(X3,X1)
            | ~ r1_tarski(X3,sK3(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK3(X0,X1),X0)
        & m1_setfam_1(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( v1_finset_1(X5)
          & m1_setfam_1(X5,X1)
          & r1_tarski(X5,X4)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK4(X0,X1,X4))
        & m1_setfam_1(sK4(X0,X1,X4),X1)
        & r1_tarski(sK4(X0,X1,X4),X4)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( v1_finset_1(X5)
                      & m1_setfam_1(X5,X1)
                      & r1_tarski(X5,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( v1_finset_1(X3)
                      & m1_setfam_1(X3,X1)
                      & r1_tarski(X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X2,X0)
                  | ~ m1_setfam_1(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',d7_compts_1)).

fof(f78,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | m1_setfam_1(sK2(X0,X3),u1_struct_0(X0))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ v1_finset_1(X2)
                | ~ m1_setfam_1(X2,u1_struct_0(X0))
                | ~ r1_tarski(X2,sK1(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & v1_tops_2(sK1(X0),X0)
            & m1_setfam_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ( v1_finset_1(sK2(X0,X3))
                & m1_setfam_1(sK2(X0,X3),u1_struct_0(X0))
                & r1_tarski(sK2(X0,X3),X3)
                & m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f51,f53,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v1_finset_1(X2)
              | ~ m1_setfam_1(X2,u1_struct_0(X0))
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X1,X0)
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X2] :
            ( ~ v1_finset_1(X2)
            | ~ m1_setfam_1(X2,u1_struct_0(X0))
            | ~ r1_tarski(X2,sK1(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK1(X0),X0)
        & m1_setfam_1(sK1(X0),u1_struct_0(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( v1_finset_1(X4)
          & m1_setfam_1(X4,u1_struct_0(X0))
          & r1_tarski(X4,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK2(X0,X3))
        & m1_setfam_1(sK2(X0,X3),u1_struct_0(X0))
        & r1_tarski(sK2(X0,X3),X3)
        & m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v1_finset_1(X4)
                  & m1_setfam_1(X4,u1_struct_0(X0))
                  & r1_tarski(X4,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( v1_finset_1(X2)
                  & m1_setfam_1(X2,u1_struct_0(X0))
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_setfam_1(X1,u1_struct_0(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( v1_finset_1(X2)
                        & m1_setfam_1(X2,u1_struct_0(X0))
                        & r1_tarski(X2,X1) ) )
                & v1_tops_2(X1,X0)
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',d3_compts_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(sK3(X0,X1),X0)
      | v2_compts_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f5629,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f75,f90,f88,f3982])).

fof(f3982,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_compts_1(X1)
      | ~ m1_setfam_1(sK2(X1,sK3(X1,X0)),X0)
      | ~ m1_setfam_1(sK3(X1,X0),u1_struct_0(X1))
      | ~ m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_tops_2(sK3(X1,X0),X1)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f3981])).

fof(f3981,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_compts_1(X1)
      | ~ m1_setfam_1(sK2(X1,sK3(X1,X0)),X0)
      | ~ m1_setfam_1(sK3(X1,X0),u1_struct_0(X1))
      | ~ m1_setfam_1(sK3(X1,X0),u1_struct_0(X1))
      | ~ m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_compts_1(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_tops_2(sK3(X1,X0),X1)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f1508,f1059])).

fof(f1059,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK2(X0,X1),k1_zfmisc_1(k2_struct_0(X0)))
      | ~ m1_setfam_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f986,f73])).

fof(f986,plain,(
    ! [X14,X15] :
      ( r1_tarski(sK2(X15,X14),k1_zfmisc_1(u1_struct_0(X15)))
      | ~ m1_setfam_1(X14,u1_struct_0(X15))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
      | ~ v1_compts_1(X15)
      | ~ l1_pre_topc(X15)
      | ~ v1_tops_2(X14,X15) ) ),
    inference(resolution,[],[f76,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t3_subset)).

fof(f76,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK2(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1508,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,sK3(X0,X1)),k1_zfmisc_1(k2_struct_0(X0)))
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f75,f449,f1507])).

fof(f1507,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | ~ v1_finset_1(sK2(X0,sK3(X0,X1)))
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X0)
      | ~ r1_tarski(sK2(X0,sK3(X0,X1)),k1_zfmisc_1(k2_struct_0(X0)))
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f1501])).

fof(f1501,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | ~ v1_finset_1(sK2(X0,sK3(X0,X1)))
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X0)
      | ~ r1_tarski(sK2(X0,sK3(X0,X1)),k1_zfmisc_1(k2_struct_0(X0)))
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f1490,f598])).

fof(f598,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK2(X3,sK3(X3,X4)),sK3(X3,X4))
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(global_subsumption,[],[f90,f596])).

fof(f596,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK3(X3,X4),X3)
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | r1_tarski(sK2(X3,sK3(X3,X4)),sK3(X3,X4))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK3(X3,X4),X3)
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | r1_tarski(sK2(X3,sK3(X3,X4)),sK3(X3,X4))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f77,f88])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | r1_tarski(sK2(X0,X3),X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1490,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK3(X2,X1))
      | ~ m1_setfam_1(X0,X1)
      | ~ v1_finset_1(X0)
      | v2_compts_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ l1_struct_0(X2)
      | ~ r1_tarski(X0,k1_zfmisc_1(k2_struct_0(X2))) ) ),
    inference(resolution,[],[f1121,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(X0))))
      | ~ v1_finset_1(X1)
      | ~ m1_setfam_1(X1,X2)
      | ~ r1_tarski(X1,sK3(X0,X2))
      | v2_compts_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f91,f73])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_finset_1(X3)
      | ~ m1_setfam_1(X3,X1)
      | ~ r1_tarski(X3,sK3(X0,X1))
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f449,plain,(
    ! [X4,X3] :
      ( ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | v1_finset_1(sK2(X3,sK3(X3,X4)))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(global_subsumption,[],[f90,f447])).

fof(f447,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK3(X3,X4),X3)
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | v1_finset_1(sK2(X3,sK3(X3,X4)))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK3(X3,X4),X3)
      | ~ m1_setfam_1(sK3(X3,X4),u1_struct_0(X3))
      | v1_finset_1(sK2(X3,sK3(X3,X4)))
      | ~ v1_compts_1(X3)
      | ~ l1_pre_topc(X3)
      | v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f79,f88])).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | v1_finset_1(sK2(X0,X3))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',dt_k2_struct_0)).

fof(f266,plain,(
    ! [X4] :
      ( m1_setfam_1(sK3(X4,k2_struct_0(X4)),k2_struct_0(X4))
      | v2_compts_1(k2_struct_0(X4),X4)
      | ~ l1_pre_topc(X4)
      | ~ l1_struct_0(X4) ) ),
    inference(resolution,[],[f89,f74])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_setfam_1(sK3(X0,X1),X1)
      | v2_compts_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',dt_l1_pre_topc)).

fof(f117,plain,
    ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f6258,plain,
    ( ~ spl9_13
    | spl9_0
    | ~ spl9_5
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f6255,f113,f121,f107,f151])).

fof(f151,plain,
    ( spl9_13
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f107,plain,
    ( spl9_0
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f113,plain,
    ( spl9_2
  <=> v2_compts_1(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f6255,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_compts_1(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl9_2 ),
    inference(resolution,[],[f6253,f114])).

fof(f114,plain,
    ( v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f6253,plain,(
    ! [X0] :
      ( ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f6251,f73])).

fof(f6251,plain,(
    ! [X0] :
      ( ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(global_subsumption,[],[f75,f81,f169,f6249])).

fof(f6249,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0)))
      | ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f6246,f73])).

fof(f6246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK1(X0),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f6240])).

fof(f6240,plain,(
    ! [X0] :
      ( ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | ~ m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(resolution,[],[f6239,f1489])).

fof(f1489,plain,(
    ! [X4,X3] :
      ( m1_setfam_1(sK4(X3,X4,sK1(X3)),X4)
      | ~ m1_setfam_1(sK1(X3),X4)
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3) ) ),
    inference(global_subsumption,[],[f82,f1488])).

fof(f1488,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK1(X3),X3)
      | ~ m1_setfam_1(sK1(X3),X4)
      | m1_setfam_1(sK4(X3,X4,sK1(X3)),X4)
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f1478])).

fof(f1478,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK1(X3),X3)
      | ~ m1_setfam_1(sK1(X3),X4)
      | m1_setfam_1(sK4(X3,X4,sK1(X3)),X4)
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | m1_setfam_1(sK4(X0,X1,X4),X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f82,plain,(
    ! [X0] :
      ( v1_tops_2(sK1(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6239,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK4(X0,X1,sK1(X0)),u1_struct_0(X0))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK1(X0),X1) ) ),
    inference(global_subsumption,[],[f82,f80,f1256,f6238])).

fof(f6238,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK1(X0),X1)
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_finset_1(sK4(X0,X1,sK1(X0)))
      | ~ m1_setfam_1(sK4(X0,X1,sK1(X0)),u1_struct_0(X0))
      | ~ v1_tops_2(sK1(X0),X0)
      | v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f6233])).

fof(f6233,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK1(X0),X1)
      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_finset_1(sK4(X0,X1,sK1(X0)))
      | ~ m1_setfam_1(sK4(X0,X1,sK1(X0)),u1_struct_0(X0))
      | ~ v1_tops_2(sK1(X0),X0)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(sK1(X0),X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(resolution,[],[f1552,f1426])).

fof(f1426,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK4(X3,X4,sK1(X3)),sK1(X3))
      | ~ m1_setfam_1(sK1(X3),X4)
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3) ) ),
    inference(global_subsumption,[],[f82,f1425])).

fof(f1425,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK1(X3),X3)
      | ~ m1_setfam_1(sK1(X3),X4)
      | r1_tarski(sK4(X3,X4,sK1(X3)),sK1(X3))
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f1415])).

fof(f1415,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK1(X3),X3)
      | ~ m1_setfam_1(sK1(X3),X4)
      | r1_tarski(sK4(X3,X4,sK1(X3)),sK1(X3))
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f85,f80])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | r1_tarski(sK4(X0,X1,X4),X4)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1552,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(sK4(X10,X11,X9),sK1(X10))
      | ~ m1_setfam_1(X9,X11)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
      | ~ v2_compts_1(X11,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ l1_pre_topc(X10)
      | ~ v1_finset_1(sK4(X10,X11,X9))
      | ~ m1_setfam_1(sK4(X10,X11,X9),u1_struct_0(X10))
      | ~ v1_tops_2(X9,X10)
      | v1_compts_1(X10) ) ),
    inference(duplicate_literal_removal,[],[f1534])).

fof(f1534,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_tops_2(X9,X10)
      | ~ m1_setfam_1(X9,X11)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
      | ~ v2_compts_1(X11,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ l1_pre_topc(X10)
      | ~ v1_finset_1(sK4(X10,X11,X9))
      | ~ m1_setfam_1(sK4(X10,X11,X9),u1_struct_0(X10))
      | ~ r1_tarski(sK4(X10,X11,X9),sK1(X10))
      | v1_compts_1(X10)
      | ~ l1_pre_topc(X10) ) ),
    inference(resolution,[],[f84,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_finset_1(X2)
      | ~ m1_setfam_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X2,sK1(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1256,plain,(
    ! [X4,X3] :
      ( v1_finset_1(sK4(X3,X4,sK1(X3)))
      | ~ m1_setfam_1(sK1(X3),X4)
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3) ) ),
    inference(global_subsumption,[],[f82,f1255])).

fof(f1255,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK1(X3),X3)
      | ~ m1_setfam_1(sK1(X3),X4)
      | v1_finset_1(sK4(X3,X4,sK1(X3)))
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f1245])).

fof(f1245,plain,(
    ! [X4,X3] :
      ( ~ v1_tops_2(sK1(X3),X3)
      | ~ m1_setfam_1(sK1(X3),X4)
      | v1_finset_1(sK4(X3,X4,sK1(X3)))
      | ~ v2_compts_1(X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | v1_compts_1(X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f87,f80])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | v1_finset_1(sK4(X0,X1,X4))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f169,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f74,f73])).

fof(f81,plain,(
    ! [X0] :
      ( m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f163,plain,
    ( spl9_14
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f149,f145,f161])).

fof(f161,plain,
    ( spl9_14
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f145,plain,
    ( spl9_10
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f149,plain,
    ( l1_struct_0(sK8)
    | ~ spl9_10 ),
    inference(resolution,[],[f75,f146])).

fof(f146,plain,
    ( l1_pre_topc(sK8)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f156,plain,
    ( spl9_12
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f148,f124,f154])).

fof(f154,plain,
    ( spl9_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f124,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f148,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f75,f125])).

fof(f125,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f147,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f105,f145])).

fof(f105,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_pre_topc(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f67])).

fof(f67,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK8) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',existence_l1_pre_topc)).

fof(f140,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f104,f138])).

fof(f138,plain,
    ( spl9_8
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f104,plain,(
    l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    l1_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f65])).

fof(f65,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK7) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',existence_l1_struct_0)).

fof(f133,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f72,f131])).

fof(f131,plain,
    ( spl9_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f72,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',dt_o_0_0_xboole_0)).

fof(f126,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f69,f124])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
      | ~ v1_compts_1(sK0) )
    & ( v2_compts_1(k2_struct_0(sK0),sK0)
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0) )
   => ( ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
        | ~ v1_compts_1(sK0) )
      & ( v2_compts_1(k2_struct_0(sK0),sK0)
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> v2_compts_1(k2_struct_0(X0),X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v1_compts_1(X0)
        <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t10_compts_1)).

fof(f119,plain,
    ( spl9_0
    | spl9_2 ),
    inference(avatar_split_clause,[],[f70,f113,f107])).

fof(f70,plain,
    ( v2_compts_1(k2_struct_0(sK0),sK0)
    | v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f71,f116,f110])).

fof(f71,plain,
    ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
