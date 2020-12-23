%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2048+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 133 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  192 ( 792 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4870,plain,(
    $false ),
    inference(global_subsumption,[],[f4784,f4866])).

fof(f4866,plain,(
    ~ m1_subset_1(u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f4736,f4638])).

fof(f4638,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f4525])).

fof(f4525,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1216])).

fof(f1216,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f4736,plain,(
    ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f4610,f4611,f4612,f4613,f4614,f4615,f4688])).

fof(f4688,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4620])).

fof(f4620,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_yellow19(X2,X0,X1)
      | k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4579])).

fof(f4579,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK5(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK5(X0,X1,X2)))) = X2
                    & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f4577,f4578])).

fof(f4578,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK5(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK5(X0,X1,X2)))) = X2
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4577,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X4] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4576])).

fof(f4576,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4511])).

fof(f4511,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4510])).

fof(f4510,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4488])).

fof(f4488,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow19)).

fof(f4615,plain,(
    ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),sK1,sK2) ),
    inference(cnf_transformation,[],[f4573])).

fof(f4573,plain,
    ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_waybel_0(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f4505,f4572,f4571,f4570])).

fof(f4570,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X1,X2)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X1,X2))),sK1,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4571,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X1,X2)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X1,X2))),sK1,X1)
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X2)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X2))),sK1,sK2)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & l1_waybel_0(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f4572,plain,
    ( ? [X2] :
        ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X2)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X2))),sK1,sK2)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f4505,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4504])).

fof(f4504,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4502])).

fof(f4502,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4501])).

fof(f4501,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow19)).

fof(f4614,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f4573])).

fof(f4613,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f4573])).

fof(f4612,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f4573])).

fof(f4611,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f4573])).

fof(f4610,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f4573])).

fof(f4784,plain,(
    m1_subset_1(u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f4611,f4724,f4651])).

fof(f4651,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4531])).

fof(f4531,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f4530])).

fof(f4530,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3203])).

fof(f3203,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f4724,plain,(
    l1_waybel_0(k4_waybel_9(sK1,sK2,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f4610,f4611,f4612,f4613,f4614,f4656])).

fof(f4656,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4535])).

fof(f4535,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4534])).

fof(f4534,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4356])).

fof(f4356,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).
%------------------------------------------------------------------------------
