%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2022+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 366 expanded)
%              Number of leaves         :    7 ( 153 expanded)
%              Depth                    :    9
%              Number of atoms          :  167 (2198 expanded)
%              Number of equality atoms :    8 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4831,plain,(
    $false ),
    inference(global_subsumption,[],[f4829,f4830])).

fof(f4830,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(superposition,[],[f4718,f4716])).

fof(f4716,plain,(
    sK2 = sK17(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f4509,f4510,f4511,f4512,f4513,f4573])).

fof(f4573,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | sK17(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f4501])).

fof(f4501,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK17(X0,X1,X2),X0)
                & r2_hidden(X1,sK17(X0,X1,X2))
                & sK17(X0,X1,X2) = X2
                & m1_subset_1(sK17(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f4450,f4500])).

fof(f4500,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK17(X0,X1,X2),X0)
        & r2_hidden(X1,sK17(X0,X1,X2))
        & sK17(X0,X1,X2) = X2
        & m1_subset_1(sK17(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4450,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4449])).

fof(f4449,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4079])).

fof(f4079,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f4513,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f4458])).

fof(f4458,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4402,f4457,f4456,f4455])).

fof(f4455,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f4456,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_connsp_2(X2,sK0,X1)
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ m1_connsp_2(X2,sK0,sK1)
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f4457,plain,
    ( ? [X2] :
        ( ~ m1_connsp_2(X2,sK0,sK1)
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f4402,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4401])).

fof(f4401,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4390])).

fof(f4390,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4389])).

fof(f4389,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f4512,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f4458])).

fof(f4511,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f4458])).

fof(f4510,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f4458])).

fof(f4509,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4458])).

fof(f4718,plain,(
    v3_pre_topc(sK17(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f4509,f4510,f4511,f4512,f4513,f4575])).

fof(f4575,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK17(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f4501])).

fof(f4829,plain,(
    ~ v3_pre_topc(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f4509,f4510,f4511,f4514,f4512,f4719,f4828,f4544])).

fof(f4544,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f4428])).

fof(f4428,plain,(
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
    inference(flattening,[],[f4427])).

fof(f4427,plain,(
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

fof(f4828,plain,(
    r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f4717,f4716])).

fof(f4717,plain,(
    r2_hidden(sK1,sK17(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f4509,f4510,f4511,f4512,f4513,f4574])).

fof(f4574,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,sK17(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f4501])).

fof(f4719,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f4715,f4716])).

fof(f4715,plain,(
    m1_subset_1(sK17(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f4509,f4510,f4511,f4512,f4513,f4572])).

fof(f4572,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4501])).

fof(f4514,plain,(
    ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f4458])).
%------------------------------------------------------------------------------
