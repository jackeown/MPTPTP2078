%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1148+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:10 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 127 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 589 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6893,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6888,f5757])).

fof(f5757,plain,(
    ~ v6_orders_2(sK46,sK45) ),
    inference(resolution,[],[f3808,f3806])).

fof(f3806,plain,(
    m1_subset_1(sK46,k1_zfmisc_1(u1_struct_0(sK45))) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3036,plain,
    ( ( ~ m1_subset_1(sK46,k1_zfmisc_1(u1_struct_0(sK45)))
      | ~ v6_orders_2(sK46,sK45) )
    & r2_wellord1(u1_orders_2(sK45),sK46)
    & m1_subset_1(sK46,k1_zfmisc_1(u1_struct_0(sK45)))
    & l1_orders_2(sK45) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK45,sK46])],[f1945,f3035,f3034])).

fof(f3034,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & r2_wellord1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK45)))
            | ~ v6_orders_2(X1,sK45) )
          & r2_wellord1(u1_orders_2(sK45),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK45))) )
      & l1_orders_2(sK45) ) ),
    introduced(choice_axiom,[])).

fof(f3035,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK45)))
          | ~ v6_orders_2(X1,sK45) )
        & r2_wellord1(u1_orders_2(sK45),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK45))) )
   => ( ( ~ m1_subset_1(sK46,k1_zfmisc_1(u1_struct_0(sK45)))
        | ~ v6_orders_2(sK46,sK45) )
      & r2_wellord1(u1_orders_2(sK45),sK46)
      & m1_subset_1(sK46,k1_zfmisc_1(u1_struct_0(sK45))) ) ),
    introduced(choice_axiom,[])).

fof(f1945,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f1944])).

fof(f1944,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1898])).

fof(f1898,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_wellord1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1897])).

fof(f1897,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_wellord1(u1_orders_2(X0),X1)
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_orders_2)).

fof(f3808,plain,
    ( ~ m1_subset_1(sK46,k1_zfmisc_1(u1_struct_0(sK45)))
    | ~ v6_orders_2(sK46,sK45) ),
    inference(cnf_transformation,[],[f3036])).

fof(f6888,plain,(
    v6_orders_2(sK46,sK45) ),
    inference(resolution,[],[f6820,f5743])).

fof(f5743,plain,
    ( ~ r7_relat_2(u1_orders_2(sK45),sK46)
    | v6_orders_2(sK46,sK45) ),
    inference(subsumption_resolution,[],[f5716,f3805])).

fof(f3805,plain,(
    l1_orders_2(sK45) ),
    inference(cnf_transformation,[],[f3036])).

fof(f5716,plain,
    ( ~ r7_relat_2(u1_orders_2(sK45),sK46)
    | v6_orders_2(sK46,sK45)
    | ~ l1_orders_2(sK45) ),
    inference(resolution,[],[f3806,f3838])).

fof(f3838,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3052])).

fof(f3052,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f1957])).

fof(f1957,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1864])).

fof(f1864,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(f6820,plain,(
    r7_relat_2(u1_orders_2(sK45),sK46) ),
    inference(subsumption_resolution,[],[f6819,f6479])).

fof(f6479,plain,(
    v1_relat_1(u1_orders_2(sK45)) ),
    inference(resolution,[],[f5695,f3888])).

fof(f3888,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1997])).

fof(f1997,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f5695,plain,(
    m1_subset_1(u1_orders_2(sK45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK45),u1_struct_0(sK45)))) ),
    inference(resolution,[],[f3805,f3866])).

fof(f3866,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f1976])).

fof(f1976,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1874])).

fof(f1874,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f6819,plain,
    ( r7_relat_2(u1_orders_2(sK45),sK46)
    | ~ v1_relat_1(u1_orders_2(sK45)) ),
    inference(subsumption_resolution,[],[f6817,f6589])).

fof(f6589,plain,(
    r6_relat_2(u1_orders_2(sK45),sK46) ),
    inference(resolution,[],[f6479,f5704])).

fof(f5704,plain,
    ( ~ v1_relat_1(u1_orders_2(sK45))
    | r6_relat_2(u1_orders_2(sK45),sK46) ),
    inference(resolution,[],[f3807,f3851])).

fof(f3851,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3060])).

fof(f3060,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3059])).

fof(f3059,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1966])).

fof(f1966,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1134])).

fof(f1134,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(f3807,plain,(
    r2_wellord1(u1_orders_2(sK45),sK46) ),
    inference(cnf_transformation,[],[f3036])).

fof(f6817,plain,
    ( ~ r6_relat_2(u1_orders_2(sK45),sK46)
    | r7_relat_2(u1_orders_2(sK45),sK46)
    | ~ v1_relat_1(u1_orders_2(sK45)) ),
    inference(resolution,[],[f6592,f4471])).

fof(f4471,plain,(
    ! [X0,X1] :
      ( ~ r1_relat_2(X1,X0)
      | ~ r6_relat_2(X1,X0)
      | r7_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3379])).

fof(f3379,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f3378])).

fof(f3378,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f2358])).

fof(f2358,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1899])).

fof(f1899,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

fof(f6592,plain,(
    r1_relat_2(u1_orders_2(sK45),sK46) ),
    inference(resolution,[],[f6479,f5701])).

fof(f5701,plain,
    ( ~ v1_relat_1(u1_orders_2(sK45))
    | r1_relat_2(u1_orders_2(sK45),sK46) ),
    inference(resolution,[],[f3807,f3848])).

fof(f3848,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3060])).
%------------------------------------------------------------------------------
