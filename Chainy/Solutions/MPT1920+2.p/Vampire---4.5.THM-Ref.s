%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1920+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 20.49s
% Output     : Refutation 20.49s
% Verified   : 
% Statistics : Number of formulae       :  112 (1031 expanded)
%              Number of leaves         :   14 ( 452 expanded)
%              Depth                    :   16
%              Number of atoms          :  350 (5038 expanded)
%              Number of equality atoms :   44 (  85 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24927,plain,(
    $false ),
    inference(subsumption_resolution,[],[f24926,f13316])).

fof(f13316,plain,(
    u1_waybel_0(sK13,sK16) != k7_relat_1(u1_waybel_0(sK13,sK14),u1_struct_0(sK16)) ),
    inference(resolution,[],[f13314,f6451])).

fof(f6451,plain,
    ( ~ m1_yellow_0(sK16,sK14)
    | u1_waybel_0(sK13,sK16) != k7_relat_1(u1_waybel_0(sK13,sK14),u1_struct_0(sK16)) ),
    inference(backward_demodulation,[],[f4983,f6445])).

fof(f6445,plain,(
    ! [X76] : k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),X76) = k7_relat_1(u1_waybel_0(sK13,sK14),X76) ),
    inference(subsumption_resolution,[],[f6332,f4878])).

fof(f4878,plain,(
    v1_funct_1(u1_waybel_0(sK13,sK14)) ),
    inference(subsumption_resolution,[],[f4863,f4397])).

fof(f4397,plain,(
    l1_struct_0(sK13) ),
    inference(cnf_transformation,[],[f4210])).

fof(f4210,plain,
    ( ~ m1_yellow_6(sK16,sK13,sK14)
    & m1_yellow_6(sK16,sK13,sK15)
    & m1_yellow_6(sK15,sK13,sK14)
    & l1_waybel_0(sK14,sK13)
    & l1_struct_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f3874,f4209,f4208,f4207,f4206])).

fof(f4206,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_yellow_6(X3,X0,X1)
                    & m1_yellow_6(X3,X0,X2) )
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_yellow_6(X3,sK13,X1)
                  & m1_yellow_6(X3,sK13,X2) )
              & m1_yellow_6(X2,sK13,X1) )
          & l1_waybel_0(X1,sK13) )
      & l1_struct_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f4207,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_yellow_6(X3,sK13,X1)
                & m1_yellow_6(X3,sK13,X2) )
            & m1_yellow_6(X2,sK13,X1) )
        & l1_waybel_0(X1,sK13) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_yellow_6(X3,sK13,sK14)
              & m1_yellow_6(X3,sK13,X2) )
          & m1_yellow_6(X2,sK13,sK14) )
      & l1_waybel_0(sK14,sK13) ) ),
    introduced(choice_axiom,[])).

fof(f4208,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_yellow_6(X3,sK13,sK14)
            & m1_yellow_6(X3,sK13,X2) )
        & m1_yellow_6(X2,sK13,sK14) )
   => ( ? [X3] :
          ( ~ m1_yellow_6(X3,sK13,sK14)
          & m1_yellow_6(X3,sK13,sK15) )
      & m1_yellow_6(sK15,sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f4209,plain,
    ( ? [X3] :
        ( ~ m1_yellow_6(X3,sK13,sK14)
        & m1_yellow_6(X3,sK13,sK15) )
   => ( ~ m1_yellow_6(sK16,sK13,sK14)
      & m1_yellow_6(sK16,sK13,sK15) ) ),
    introduced(choice_axiom,[])).

fof(f3874,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_yellow_6(X3,X0,X1)
                  & m1_yellow_6(X3,X0,X2) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3864])).

fof(f3864,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_yellow_6(X3,X0,X2)
                   => m1_yellow_6(X3,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f3863])).

fof(f3863,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_yellow_6(X3,X0,X2)
                 => m1_yellow_6(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_6)).

fof(f4863,plain,
    ( v1_funct_1(u1_waybel_0(sK13,sK14))
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4398,f4435])).

fof(f4435,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3909])).

fof(f3909,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f3908])).

fof(f3908,plain,(
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

fof(f4398,plain,(
    l1_waybel_0(sK14,sK13) ),
    inference(cnf_transformation,[],[f4210])).

fof(f6332,plain,(
    ! [X76] :
      ( k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),X76) = k7_relat_1(u1_waybel_0(sK13,sK14),X76)
      | ~ v1_funct_1(u1_waybel_0(sK13,sK14)) ) ),
    inference(resolution,[],[f4880,f4420])).

fof(f4420,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3895])).

fof(f3895,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3894])).

fof(f3894,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1554])).

fof(f1554,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f4880,plain,(
    m1_subset_1(u1_waybel_0(sK13,sK14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13)))) ),
    inference(subsumption_resolution,[],[f4865,f4397])).

fof(f4865,plain,
    ( m1_subset_1(u1_waybel_0(sK13,sK14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4398,f4437])).

fof(f4437,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3909])).

fof(f4983,plain,
    ( u1_waybel_0(sK13,sK16) != k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),u1_struct_0(sK16))
    | ~ m1_yellow_0(sK16,sK14) ),
    inference(subsumption_resolution,[],[f4982,f4397])).

fof(f4982,plain,
    ( u1_waybel_0(sK13,sK16) != k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),u1_struct_0(sK16))
    | ~ m1_yellow_0(sK16,sK14)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4981,f4398])).

fof(f4981,plain,
    ( u1_waybel_0(sK13,sK16) != k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),u1_struct_0(sK16))
    | ~ m1_yellow_0(sK16,sK14)
    | ~ l1_waybel_0(sK14,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4980,f4949])).

fof(f4949,plain,(
    l1_waybel_0(sK16,sK13) ),
    inference(subsumption_resolution,[],[f4948,f4397])).

fof(f4948,plain,
    ( l1_waybel_0(sK16,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4943,f4911])).

fof(f4911,plain,(
    l1_waybel_0(sK15,sK13) ),
    inference(subsumption_resolution,[],[f4910,f4397])).

fof(f4910,plain,
    ( l1_waybel_0(sK15,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4905,f4398])).

fof(f4905,plain,
    ( l1_waybel_0(sK15,sK13)
    | ~ l1_waybel_0(sK14,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4399,f4403])).

fof(f4403,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3878])).

fof(f3878,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f3877])).

fof(f3877,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3810])).

fof(f3810,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f4399,plain,(
    m1_yellow_6(sK15,sK13,sK14) ),
    inference(cnf_transformation,[],[f4210])).

fof(f4943,plain,
    ( l1_waybel_0(sK16,sK13)
    | ~ l1_waybel_0(sK15,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4400,f4403])).

fof(f4400,plain,(
    m1_yellow_6(sK16,sK13,sK15) ),
    inference(cnf_transformation,[],[f4210])).

fof(f4980,plain,
    ( u1_waybel_0(sK13,sK16) != k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),u1_struct_0(sK16))
    | ~ m1_yellow_0(sK16,sK14)
    | ~ l1_waybel_0(sK16,sK13)
    | ~ l1_waybel_0(sK14,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4401,f4406])).

fof(f4406,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_6(X2,X0,X1)
      | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
      | ~ m1_yellow_0(X2,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4214])).

fof(f4214,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f4213])).

fof(f4213,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3879])).

fof(f3879,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3803])).

fof(f3803,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f4401,plain,(
    ~ m1_yellow_6(sK16,sK13,sK14) ),
    inference(cnf_transformation,[],[f4210])).

fof(f13314,plain,(
    m1_yellow_0(sK16,sK14) ),
    inference(subsumption_resolution,[],[f13303,f5487])).

fof(f5487,plain,(
    m1_yellow_0(sK15,sK14) ),
    inference(resolution,[],[f4907,f4911])).

fof(f4907,plain,
    ( ~ l1_waybel_0(sK15,sK13)
    | m1_yellow_0(sK15,sK14) ),
    inference(subsumption_resolution,[],[f4906,f4397])).

fof(f4906,plain,
    ( m1_yellow_0(sK15,sK14)
    | ~ l1_waybel_0(sK15,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4903,f4398])).

fof(f4903,plain,
    ( m1_yellow_0(sK15,sK14)
    | ~ l1_waybel_0(sK15,sK13)
    | ~ l1_waybel_0(sK14,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4399,f4404])).

fof(f4404,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4214])).

fof(f13303,plain,
    ( m1_yellow_0(sK16,sK14)
    | ~ m1_yellow_0(sK15,sK14) ),
    inference(resolution,[],[f4886,f5504])).

fof(f5504,plain,(
    m1_yellow_0(sK16,sK15) ),
    inference(resolution,[],[f4945,f4949])).

fof(f4945,plain,
    ( ~ l1_waybel_0(sK16,sK13)
    | m1_yellow_0(sK16,sK15) ),
    inference(subsumption_resolution,[],[f4944,f4397])).

fof(f4944,plain,
    ( m1_yellow_0(sK16,sK15)
    | ~ l1_waybel_0(sK16,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4941,f4911])).

fof(f4941,plain,
    ( m1_yellow_0(sK16,sK15)
    | ~ l1_waybel_0(sK16,sK13)
    | ~ l1_waybel_0(sK15,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4400,f4404])).

fof(f4886,plain,(
    ! [X2,X3] :
      ( ~ m1_yellow_0(X2,X3)
      | m1_yellow_0(X2,sK14)
      | ~ m1_yellow_0(X3,sK14) ) ),
    inference(resolution,[],[f4877,f4442])).

fof(f4442,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X0)
      | ~ m1_yellow_0(X2,X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3917])).

fof(f3917,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_yellow_0(X2,X0)
              | ~ m1_yellow_0(X2,X1) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3861])).

fof(f3861,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_6)).

fof(f4877,plain,(
    l1_orders_2(sK14) ),
    inference(subsumption_resolution,[],[f4862,f4397])).

fof(f4862,plain,
    ( l1_orders_2(sK14)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4398,f4409])).

fof(f4409,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3882])).

fof(f3882,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3197])).

fof(f3197,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f24926,plain,(
    u1_waybel_0(sK13,sK16) = k7_relat_1(u1_waybel_0(sK13,sK14),u1_struct_0(sK16)) ),
    inference(forward_demodulation,[],[f24916,f23876])).

fof(f23876,plain,(
    u1_waybel_0(sK13,sK16) = k7_relat_1(u1_waybel_0(sK13,sK15),u1_struct_0(sK16)) ),
    inference(subsumption_resolution,[],[f23875,f4975])).

fof(f4975,plain,(
    v1_funct_1(u1_waybel_0(sK13,sK15)) ),
    inference(subsumption_resolution,[],[f4960,f4397])).

fof(f4960,plain,
    ( v1_funct_1(u1_waybel_0(sK13,sK15))
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4911,f4435])).

fof(f23875,plain,
    ( u1_waybel_0(sK13,sK16) = k7_relat_1(u1_waybel_0(sK13,sK15),u1_struct_0(sK16))
    | ~ v1_funct_1(u1_waybel_0(sK13,sK15)) ),
    inference(subsumption_resolution,[],[f23836,f4977])).

fof(f4977,plain,(
    m1_subset_1(u1_waybel_0(sK13,sK15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13)))) ),
    inference(subsumption_resolution,[],[f4962,f4397])).

fof(f4962,plain,
    ( m1_subset_1(u1_waybel_0(sK13,sK15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4911,f4437])).

fof(f23836,plain,
    ( u1_waybel_0(sK13,sK16) = k7_relat_1(u1_waybel_0(sK13,sK15),u1_struct_0(sK16))
    | ~ m1_subset_1(u1_waybel_0(sK13,sK15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
    | ~ v1_funct_1(u1_waybel_0(sK13,sK15)) ),
    inference(superposition,[],[f7227,f4420])).

fof(f7227,plain,(
    u1_waybel_0(sK13,sK16) = k2_partfun1(u1_struct_0(sK15),u1_struct_0(sK13),u1_waybel_0(sK13,sK15),u1_struct_0(sK16)) ),
    inference(resolution,[],[f4947,f4949])).

fof(f4947,plain,
    ( ~ l1_waybel_0(sK16,sK13)
    | u1_waybel_0(sK13,sK16) = k2_partfun1(u1_struct_0(sK15),u1_struct_0(sK13),u1_waybel_0(sK13,sK15),u1_struct_0(sK16)) ),
    inference(subsumption_resolution,[],[f4946,f4397])).

fof(f4946,plain,
    ( u1_waybel_0(sK13,sK16) = k2_partfun1(u1_struct_0(sK15),u1_struct_0(sK13),u1_waybel_0(sK13,sK15),u1_struct_0(sK16))
    | ~ l1_waybel_0(sK16,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4942,f4911])).

fof(f4942,plain,
    ( u1_waybel_0(sK13,sK16) = k2_partfun1(u1_struct_0(sK15),u1_struct_0(sK13),u1_waybel_0(sK13,sK15),u1_struct_0(sK16))
    | ~ l1_waybel_0(sK16,sK13)
    | ~ l1_waybel_0(sK15,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4400,f4405])).

fof(f4405,plain,(
    ! [X2,X0,X1] :
      ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4214])).

fof(f24916,plain,(
    k7_relat_1(u1_waybel_0(sK13,sK14),u1_struct_0(sK16)) = k7_relat_1(u1_waybel_0(sK13,sK15),u1_struct_0(sK16)) ),
    inference(resolution,[],[f6680,f5517])).

fof(f5517,plain,(
    r1_tarski(u1_struct_0(sK16),u1_struct_0(sK15)) ),
    inference(subsumption_resolution,[],[f5516,f4974])).

fof(f4974,plain,(
    l1_orders_2(sK15) ),
    inference(subsumption_resolution,[],[f4959,f4397])).

fof(f4959,plain,
    ( l1_orders_2(sK15)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4911,f4409])).

fof(f5516,plain,
    ( r1_tarski(u1_struct_0(sK16),u1_struct_0(sK15))
    | ~ l1_orders_2(sK15) ),
    inference(subsumption_resolution,[],[f5511,f5028])).

fof(f5028,plain,(
    l1_orders_2(sK16) ),
    inference(subsumption_resolution,[],[f5013,f4397])).

fof(f5013,plain,
    ( l1_orders_2(sK16)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4949,f4409])).

fof(f5511,plain,
    ( r1_tarski(u1_struct_0(sK16),u1_struct_0(sK15))
    | ~ l1_orders_2(sK16)
    | ~ l1_orders_2(sK15) ),
    inference(resolution,[],[f5504,f4444])).

fof(f4444,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4228])).

fof(f4228,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4227])).

fof(f4227,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3919])).

fof(f3919,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2976])).

fof(f2976,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f6680,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,u1_struct_0(sK15))
      | k7_relat_1(u1_waybel_0(sK13,sK14),X6) = k7_relat_1(u1_waybel_0(sK13,sK15),X6) ) ),
    inference(subsumption_resolution,[],[f6679,f6348])).

fof(f6348,plain,(
    v1_relat_1(u1_waybel_0(sK13,sK14)) ),
    inference(resolution,[],[f4880,f4506])).

fof(f4506,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f3954])).

fof(f3954,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f6679,plain,(
    ! [X6] :
      ( k7_relat_1(u1_waybel_0(sK13,sK14),X6) = k7_relat_1(u1_waybel_0(sK13,sK15),X6)
      | ~ r1_tarski(X6,u1_struct_0(sK15))
      | ~ v1_relat_1(u1_waybel_0(sK13,sK14)) ) ),
    inference(subsumption_resolution,[],[f6578,f4878])).

fof(f6578,plain,(
    ! [X6] :
      ( k7_relat_1(u1_waybel_0(sK13,sK14),X6) = k7_relat_1(u1_waybel_0(sK13,sK15),X6)
      | ~ r1_tarski(X6,u1_struct_0(sK15))
      | ~ v1_funct_1(u1_waybel_0(sK13,sK14))
      | ~ v1_relat_1(u1_waybel_0(sK13,sK14)) ) ),
    inference(superposition,[],[f4515,f6461])).

fof(f6461,plain,(
    u1_waybel_0(sK13,sK15) = k7_relat_1(u1_waybel_0(sK13,sK14),u1_struct_0(sK15)) ),
    inference(subsumption_resolution,[],[f6450,f4911])).

fof(f6450,plain,
    ( u1_waybel_0(sK13,sK15) = k7_relat_1(u1_waybel_0(sK13,sK14),u1_struct_0(sK15))
    | ~ l1_waybel_0(sK15,sK13) ),
    inference(backward_demodulation,[],[f4909,f6445])).

fof(f4909,plain,
    ( u1_waybel_0(sK13,sK15) = k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),u1_struct_0(sK15))
    | ~ l1_waybel_0(sK15,sK13) ),
    inference(subsumption_resolution,[],[f4908,f4397])).

fof(f4908,plain,
    ( u1_waybel_0(sK13,sK15) = k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),u1_struct_0(sK15))
    | ~ l1_waybel_0(sK15,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(subsumption_resolution,[],[f4904,f4398])).

fof(f4904,plain,
    ( u1_waybel_0(sK13,sK15) = k2_partfun1(u1_struct_0(sK14),u1_struct_0(sK13),u1_waybel_0(sK13,sK14),u1_struct_0(sK15))
    | ~ l1_waybel_0(sK15,sK13)
    | ~ l1_waybel_0(sK14,sK13)
    | ~ l1_struct_0(sK13) ),
    inference(resolution,[],[f4399,f4405])).

fof(f4515,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f3965])).

fof(f3965,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f3964])).

fof(f3964,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1044])).

fof(f1044,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).
%------------------------------------------------------------------------------
