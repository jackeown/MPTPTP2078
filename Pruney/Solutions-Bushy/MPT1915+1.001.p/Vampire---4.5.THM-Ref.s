%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:55 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  86 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :  194 ( 448 expanded)
%              Number of equality atoms :   50 ( 105 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f25])).

fof(f25,plain,(
    u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_6)).

fof(f59,plain,(
    u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(resolution,[],[f57,f21])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(X0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f46,f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

% (12902)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f46,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
      | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X4
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X4,X5) ) ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2))) ),
    inference(resolution,[],[f42,f21])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,sK1,sK2)),u1_orders_2(k3_yellow_6(X0,sK1,sK2))) ) ),
    inference(resolution,[],[f41,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0)))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f40,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0)))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f39,f23])).

fof(f23,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f38,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0) )
     => ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_6)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | k3_yellow_6(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X1)
      | ~ v6_waybel_0(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

% (12904)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v6_waybel_0(X3,X1) )
                 => ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_6)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

%------------------------------------------------------------------------------
