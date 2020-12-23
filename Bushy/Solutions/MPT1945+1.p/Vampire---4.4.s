%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t43_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:56 EDT 2019

% Result     : Theorem 196.10s
% Output     : Refutation 196.10s
% Verified   : 
% Statistics : Number of formulae       :  215 (2119 expanded)
%              Number of leaves         :   31 ( 888 expanded)
%              Depth                    :   29
%              Number of atoms          : 1369 (24186 expanded)
%              Number of equality atoms :   46 (2097 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215761,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f156,f213508,f215299,f10688])).

fof(f10688,plain,(
    ! [X33,X34] :
      ( m1_subset_1(sK18(a_3_1_yellow_6(sK0,sK1,X33),X34),u1_struct_0(sK0))
      | ~ m1_subset_1(X33,u1_struct_0(sK1))
      | r1_tarski(a_3_1_yellow_6(sK0,sK1,X33),X34) ) ),
    inference(resolution,[],[f4406,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK18(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f133,f134])).

fof(f134,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',d3_tarski)).

fof(f4406,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_3_1_yellow_6(sK0,sK1,X1))
      | m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4400,f551])).

fof(f551,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK19(X15,sK0,sK1,X16),u1_struct_0(sK1))
      | ~ r2_hidden(X15,a_3_1_yellow_6(sK0,sK1,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f550,f147])).

fof(f147,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2,k2_pre_topc(sK0,X4))
        | a_3_1_yellow_6(sK0,sK1,sK3) != X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f97,f96,f95,f94])).

fof(f94,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                        | a_3_1_yellow_6(X0,X1,X3) != X4
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & r2_hidden(X2,k10_yellow_6(X0,X1))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k2_pre_topc(sK0,X4))
                      | a_3_1_yellow_6(sK0,X1,X3) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & r2_hidden(X2,k10_yellow_6(sK0,X1))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                      | a_3_1_yellow_6(X0,X1,X3) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                    | a_3_1_yellow_6(X0,sK1,X3) != X4
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            & r2_hidden(X2,k10_yellow_6(X0,sK1))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK1,X0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                  | a_3_1_yellow_6(X0,X1,X3) != X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & r2_hidden(X2,k10_yellow_6(X0,X1))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(sK2,k2_pre_topc(X0,X4))
                | a_3_1_yellow_6(X0,X1,X3) != X4
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & r2_hidden(sK2,k10_yellow_6(X0,X1))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
              | a_3_1_yellow_6(X0,X1,X3) != X4
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
            | a_3_1_yellow_6(X0,X1,sK3) != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                      | a_3_1_yellow_6(X0,X1,X3) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                      | a_3_1_yellow_6(X0,X1,X3) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,X1))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( r2_hidden(X2,k2_pre_topc(X0,X4))
                          & a_3_1_yellow_6(X0,X1,X3) = X4
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( r2_hidden(X2,k2_pre_topc(X0,X4))
                        & a_3_1_yellow_6(X0,X1,X3) = X4
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',t43_yellow_6)).

fof(f550,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK19(X15,sK0,sK1,X16),u1_struct_0(sK1))
      | ~ r2_hidden(X15,a_3_1_yellow_6(sK0,sK1,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f549,f148])).

fof(f148,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f549,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK19(X15,sK0,sK1,X16),u1_struct_0(sK1))
      | ~ r2_hidden(X15,a_3_1_yellow_6(sK0,sK1,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f548,f149])).

fof(f149,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f548,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK19(X15,sK0,sK1,X16),u1_struct_0(sK1))
      | ~ r2_hidden(X15,a_3_1_yellow_6(sK0,sK1,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f547,f150])).

fof(f150,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f547,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK19(X15,sK0,sK1,X16),u1_struct_0(sK1))
      | ~ r2_hidden(X15,a_3_1_yellow_6(sK0,sK1,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f546,f151])).

fof(f151,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f546,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK19(X15,sK0,sK1,X16),u1_struct_0(sK1))
      | ~ r2_hidden(X15,a_3_1_yellow_6(sK0,sK1,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f497,f152])).

fof(f152,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f497,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK19(X15,sK0,sK1,X16),u1_struct_0(sK1))
      | ~ r2_hidden(X15,a_3_1_yellow_6(sK0,sK1,X16))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f153,f214])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK19(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | k2_waybel_0(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ( r1_orders_2(X2,X3,sK19(X0,X1,X2,X3))
            & k2_waybel_0(X1,X2,sK19(X0,X1,X2,X3)) = X0
            & m1_subset_1(sK19(X0,X1,X2,X3),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f138,f139])).

fof(f139,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_orders_2(X2,X3,X5)
          & k2_waybel_0(X1,X2,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r1_orders_2(X2,X3,sK19(X0,X1,X2,X3))
        & k2_waybel_0(X1,X2,sK19(X0,X1,X2,X3)) = X0
        & m1_subset_1(sK19(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f138,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | k2_waybel_0(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X5] :
              ( r1_orders_2(X2,X3,X5)
              & k2_waybel_0(X1,X2,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f137])).

fof(f137,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | k2_waybel_0(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r1_orders_2(X2,X3,X4)
              & k2_waybel_0(X1,X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & k2_waybel_0(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & k2_waybel_0(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & k2_waybel_0(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',fraenkel_a_3_1_yellow_6)).

fof(f153,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f4400,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK19(X0,sK0,sK1,X1),u1_struct_0(sK1))
      | ~ r2_hidden(X0,a_3_1_yellow_6(sK0,sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f1788,f557])).

fof(f557,plain,(
    ! [X17,X18] :
      ( k2_waybel_0(sK0,sK1,sK19(X17,sK0,sK1,X18)) = X17
      | ~ r2_hidden(X17,a_3_1_yellow_6(sK0,sK1,X18))
      | ~ m1_subset_1(X18,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f556,f147])).

fof(f556,plain,(
    ! [X17,X18] :
      ( k2_waybel_0(sK0,sK1,sK19(X17,sK0,sK1,X18)) = X17
      | ~ r2_hidden(X17,a_3_1_yellow_6(sK0,sK1,X18))
      | ~ m1_subset_1(X18,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f555,f148])).

fof(f555,plain,(
    ! [X17,X18] :
      ( k2_waybel_0(sK0,sK1,sK19(X17,sK0,sK1,X18)) = X17
      | ~ r2_hidden(X17,a_3_1_yellow_6(sK0,sK1,X18))
      | ~ m1_subset_1(X18,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f554,f149])).

fof(f554,plain,(
    ! [X17,X18] :
      ( k2_waybel_0(sK0,sK1,sK19(X17,sK0,sK1,X18)) = X17
      | ~ r2_hidden(X17,a_3_1_yellow_6(sK0,sK1,X18))
      | ~ m1_subset_1(X18,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f553,f150])).

fof(f553,plain,(
    ! [X17,X18] :
      ( k2_waybel_0(sK0,sK1,sK19(X17,sK0,sK1,X18)) = X17
      | ~ r2_hidden(X17,a_3_1_yellow_6(sK0,sK1,X18))
      | ~ m1_subset_1(X18,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f552,f151])).

fof(f552,plain,(
    ! [X17,X18] :
      ( k2_waybel_0(sK0,sK1,sK19(X17,sK0,sK1,X18)) = X17
      | ~ r2_hidden(X17,a_3_1_yellow_6(sK0,sK1,X18))
      | ~ m1_subset_1(X18,u1_struct_0(sK1))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f498,f152])).

fof(f498,plain,(
    ! [X17,X18] :
      ( k2_waybel_0(sK0,sK1,sK19(X17,sK0,sK1,X18)) = X17
      | ~ r2_hidden(X17,a_3_1_yellow_6(sK0,sK1,X18))
      | ~ m1_subset_1(X18,u1_struct_0(sK1))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f153,f215])).

fof(f215,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_waybel_0(X1,X2,sK19(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f1788,plain,(
    ! [X14] :
      ( m1_subset_1(k2_waybel_0(sK0,sK1,X14),u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f545,f310])).

fof(f310,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f149,f159])).

fof(f159,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',dt_l1_pre_topc)).

fof(f545,plain,(
    ! [X14] :
      ( m1_subset_1(k2_waybel_0(sK0,sK1,X14),u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK1))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f544,f147])).

fof(f544,plain,(
    ! [X14] :
      ( m1_subset_1(k2_waybel_0(sK0,sK1,X14),u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f496,f150])).

fof(f496,plain,(
    ! [X14] :
      ( m1_subset_1(k2_waybel_0(sK0,sK1,X14),u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f153,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',dt_k2_waybel_0)).

fof(f215299,plain,(
    ~ m1_subset_1(sK18(a_3_1_yellow_6(sK0,sK1,sK3),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f215298,f1233])).

fof(f1233,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f752,f543])).

fof(f543,plain,(
    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f542,f147])).

fof(f542,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f541,f148])).

fof(f541,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f540,f149])).

fof(f540,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f539,f150])).

fof(f539,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f538,f151])).

fof(f538,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f492,f152])).

fof(f492,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f153,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',dt_k10_yellow_6)).

fof(f752,plain,(
    ! [X5] :
      ( ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(X5))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f155,f211])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',t5_subset)).

fof(f155,plain,(
    r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f98])).

fof(f215298,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK18(a_3_1_yellow_6(sK0,sK1,sK3),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f213921,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',t2_subset)).

fof(f213921,plain,(
    ~ r2_hidden(sK18(a_3_1_yellow_6(sK0,sK1,sK3),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f213508,f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK18(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f213508,plain,(
    ~ r1_tarski(a_3_1_yellow_6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(resolution,[],[f213501,f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',t3_subset)).

fof(f213501,plain,(
    ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f213433,f3940])).

fof(f3940,plain,
    ( r1_waybel_0(sK0,sK1,sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2))
    | ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f802,f2516])).

fof(f2516,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK2)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f764,f543])).

fof(f764,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f763,f147])).

fof(f763,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f762,f148])).

fof(f762,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f761,f149])).

fof(f761,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f760,f150])).

fof(f760,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f759,f151])).

fof(f759,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f758,f152])).

fof(f758,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f757,f153])).

fof(f757,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f743,f154])).

fof(f154,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f98])).

fof(f743,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f155,f224])).

fof(f224,plain,(
    ! [X6,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
                        & m1_connsp_2(sK7(X0,X1,X2),X0,sK6(X0,X1,X2)) )
                      | ~ r2_hidden(sK6(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2)) )
                      | r2_hidden(sK6(X0,X1,X2),X2) )
                    & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
                            & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f107,f110,f109,f108])).

fof(f108,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK6(X0,X1,X2)) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK6(X0,X1,X2)) )
          | r2_hidden(sK6(X0,X1,X2),X2) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X2))
        & m1_connsp_2(sK7(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK8(X0,X1,X6))
        & m1_connsp_2(sK8(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',d18_yellow_6)).

fof(f802,plain,
    ( m1_connsp_2(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),sK0,sK2)
    | ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f801,f147])).

fof(f801,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),sK0,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f800,f148])).

fof(f800,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),sK0,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f799,f149])).

fof(f799,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),sK0,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f798,f154])).

fof(f798,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),sK0,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f793])).

fof(f793,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),sK0,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f221,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_connsp_2(sK5(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(sK5(X0,X1,X2),X1)
                    & m1_connsp_2(sK5(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f102,f103])).

fof(f103,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X3,X1)
          & m1_connsp_2(X3,X0,X2) )
     => ( r1_xboole_0(sK5(X0,X1,X2),X1)
        & m1_connsp_2(sK5(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',t34_connsp_2)).

fof(f221,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,a_3_1_yellow_6(sK0,sK1,sK3)))
    | ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK2,k2_pre_topc(sK0,X4))
      | a_3_1_yellow_6(sK0,sK1,sK3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f213433,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2))
    | ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f209875,f806])).

fof(f806,plain,
    ( r1_xboole_0(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),a_3_1_yellow_6(sK0,sK1,sK3))
    | ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f805,f147])).

fof(f805,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),a_3_1_yellow_6(sK0,sK1,sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f804,f148])).

fof(f804,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),a_3_1_yellow_6(sK0,sK1,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f803,f149])).

fof(f803,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),a_3_1_yellow_6(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f797,f154])).

fof(f797,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),a_3_1_yellow_6(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f794])).

fof(f794,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK5(sK0,a_3_1_yellow_6(sK0,sK1,sK3),sK2),a_3_1_yellow_6(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(a_3_1_yellow_6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f221,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f209875,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(X20,a_3_1_yellow_6(sK0,sK1,sK3))
      | ~ r1_waybel_0(sK0,sK1,X20) ) ),
    inference(subsumption_resolution,[],[f209874,f1710])).

fof(f1710,plain,(
    ! [X5] :
      ( m1_subset_1(sK13(sK0,sK1,X5),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X5) ) ),
    inference(subsumption_resolution,[],[f529,f310])).

fof(f529,plain,(
    ! [X5] :
      ( m1_subset_1(sK13(sK0,sK1,X5),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X5)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f528,f147])).

fof(f528,plain,(
    ! [X5] :
      ( m1_subset_1(sK13(sK0,sK1,X5),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X5)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f487,f150])).

fof(f487,plain,(
    ! [X5] :
      ( m1_subset_1(sK13(sK0,sK1,X5),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X5)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f153,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK12(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK12(X0,X1,X2,X3))
                      & m1_subset_1(sK12(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK13(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f119,f121,f120])).

fof(f120,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK12(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK12(X0,X1,X2,X3))
        & m1_subset_1(sK12(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f121,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK13(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f119,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',d11_waybel_0)).

fof(f209874,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(X20,a_3_1_yellow_6(sK0,sK1,sK3))
      | ~ r1_waybel_0(sK0,sK1,X20)
      | ~ m1_subset_1(sK13(sK0,sK1,X20),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f209873,f147])).

fof(f209873,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(X20,a_3_1_yellow_6(sK0,sK1,sK3))
      | ~ r1_waybel_0(sK0,sK1,X20)
      | ~ m1_subset_1(sK13(sK0,sK1,X20),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f209872,f148])).

fof(f209872,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(X20,a_3_1_yellow_6(sK0,sK1,sK3))
      | ~ r1_waybel_0(sK0,sK1,X20)
      | ~ m1_subset_1(sK13(sK0,sK1,X20),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f209871,f149])).

fof(f209871,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(X20,a_3_1_yellow_6(sK0,sK1,sK3))
      | ~ r1_waybel_0(sK0,sK1,X20)
      | ~ m1_subset_1(sK13(sK0,sK1,X20),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f209870,f153])).

fof(f209870,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(X20,a_3_1_yellow_6(sK0,sK1,sK3))
      | ~ r1_waybel_0(sK0,sK1,X20)
      | ~ m1_subset_1(sK13(sK0,sK1,X20),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f209783,f156])).

fof(f209783,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(X20,a_3_1_yellow_6(sK0,sK1,sK3))
      | ~ r1_waybel_0(sK0,sK1,X20)
      | ~ m1_subset_1(sK13(sK0,sK1,X20),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f11551,f2918])).

fof(f2918,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(k2_waybel_0(X7,sK1,sK11(sK1,X6,X5)),a_3_1_yellow_6(X7,sK1,X5))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,X7)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f2917,f2787])).

fof(f2787,plain,(
    ! [X10,X9] :
      ( m1_subset_1(sK11(sK1,X9,X10),u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(X9,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f462,f807])).

fof(f807,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f482,f310])).

fof(f482,plain,
    ( l1_orders_2(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f153,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',dt_l1_waybel_0)).

fof(f462,plain,(
    ! [X10,X9] :
      ( m1_subset_1(sK11(sK1,X9,X10),u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(X9,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f443,f150])).

fof(f443,plain,(
    ! [X10,X9] :
      ( m1_subset_1(sK11(sK1,X9,X10),u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(X9,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f152,f173])).

fof(f173,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK11(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ( ! [X3] :
                ( ~ r1_orders_2(X0,sK10(X0),X3)
                | ~ r1_orders_2(X0,sK9(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK10(X0),u1_struct_0(X0))
            & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ( r1_orders_2(X0,X5,sK11(X0,X4,X5))
                    & r1_orders_2(X0,X4,sK11(X0,X4,X5))
                    & m1_subset_1(sK11(X0,X4,X5),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f113,f116,f115,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK9(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK10(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK11(X0,X4,X5))
        & r1_orders_2(X0,X4,sK11(X0,X4,X5))
        & m1_subset_1(sK11(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ? [X6] :
                      ( r1_orders_2(X0,X5,X6)
                      & r1_orders_2(X0,X4,X6)
                      & m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',d5_yellow_6)).

fof(f2917,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(X7,sK1,sK11(sK1,X6,X5)),a_3_1_yellow_6(X7,sK1,X5))
      | ~ m1_subset_1(sK11(sK1,X6,X5),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,X7)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f2916,f150])).

fof(f2916,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(X7,sK1,sK11(sK1,X6,X5)),a_3_1_yellow_6(X7,sK1,X5))
      | ~ m1_subset_1(sK11(sK1,X6,X5),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,X7)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f2915,f151])).

fof(f2915,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(X7,sK1,sK11(sK1,X6,X5)),a_3_1_yellow_6(X7,sK1,X5))
      | ~ m1_subset_1(sK11(sK1,X6,X5),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,X7)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f2912,f152])).

fof(f2912,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(X7,sK1,sK11(sK1,X6,X5)),a_3_1_yellow_6(X7,sK1,X5))
      | ~ m1_subset_1(sK11(sK1,X6,X5),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,X7)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(duplicate_literal_removal,[],[f2911])).

fof(f2911,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(X7,sK1,sK11(sK1,X6,X5)),a_3_1_yellow_6(X7,sK1,X5))
      | ~ m1_subset_1(sK11(sK1,X6,X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,X7)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f2874,f225])).

fof(f225,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k2_waybel_0(X1,X2,X4),a_3_1_yellow_6(X1,X2,X3))
      | ~ r1_orders_2(X2,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f217])).

fof(f217,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      | ~ r1_orders_2(X2,X3,X4)
      | k2_waybel_0(X1,X2,X4) != X0
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f2874,plain,(
    ! [X14,X13] :
      ( r1_orders_2(sK1,X13,sK11(sK1,X14,X13))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | ~ m1_subset_1(X14,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f464,f807])).

fof(f464,plain,(
    ! [X14,X13] :
      ( r1_orders_2(sK1,X13,sK11(sK1,X14,X13))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | ~ m1_subset_1(X14,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f445,f150])).

fof(f445,plain,(
    ! [X14,X13] :
      ( r1_orders_2(sK1,X13,sK11(sK1,X14,X13))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | ~ m1_subset_1(X14,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f152,f175])).

fof(f175,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK11(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f11551,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK11(sK1,sK13(sK0,sK1,X0),sK3)),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f5134,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK15(X0,X1),X1)
          & r2_hidden(sK15(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f61,f125])).

fof(f125,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK15(X0,X1),X1)
        & r2_hidden(sK15(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t43_yellow_6.p',t3_xboole_0)).

fof(f5134,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK11(sK1,sK13(sK0,sK1,X0),sK3)),X0)
      | ~ r1_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f5133,f1710])).

fof(f5133,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK11(sK1,sK13(sK0,sK1,X0),sK3)),X0)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ m1_subset_1(sK13(sK0,sK1,X0),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f5120,f1871])).

fof(f1871,plain,(
    ! [X4] :
      ( m1_subset_1(sK11(sK1,X4,sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f690,f807])).

fof(f690,plain,(
    ! [X4] :
      ( m1_subset_1(sK11(sK1,X4,sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f689,f150])).

fof(f689,plain,(
    ! [X4] :
      ( m1_subset_1(sK11(sK1,X4,sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f661,f152])).

fof(f661,plain,(
    ! [X4] :
      ( m1_subset_1(sK11(sK1,X4,sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ v7_waybel_0(sK1)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f156,f173])).

fof(f5120,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK11(sK1,sK13(sK0,sK1,X0),sK3)),X0)
      | ~ m1_subset_1(sK11(sK1,sK13(sK0,sK1,X0),sK3),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ m1_subset_1(sK13(sK0,sK1,X0),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f5117,f2023])).

fof(f2023,plain,(
    ! [X6] :
      ( r1_orders_2(sK1,X6,sK11(sK1,X6,sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f694,f807])).

fof(f694,plain,(
    ! [X6] :
      ( r1_orders_2(sK1,X6,sK11(sK1,X6,sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f693,f150])).

fof(f693,plain,(
    ! [X6] :
      ( r1_orders_2(sK1,X6,sK11(sK1,X6,sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f663,f152])).

fof(f663,plain,(
    ! [X6] :
      ( r1_orders_2(sK1,X6,sK11(sK1,X6,sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ v7_waybel_0(sK1)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f156,f174])).

fof(f174,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK11(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f5117,plain,(
    ! [X6,X7] :
      ( ~ r1_orders_2(sK1,sK13(sK0,sK1,X7),X6)
      | r2_hidden(k2_waybel_0(sK0,sK1,X6),X7)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X7) ) ),
    inference(subsumption_resolution,[],[f531,f310])).

fof(f531,plain,(
    ! [X6,X7] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X6),X7)
      | ~ r1_orders_2(sK1,sK13(sK0,sK1,X7),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X7)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f530,f147])).

fof(f530,plain,(
    ! [X6,X7] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X6),X7)
      | ~ r1_orders_2(sK1,sK13(sK0,sK1,X7),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X7)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f488,f150])).

fof(f488,plain,(
    ! [X6,X7] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X6),X7)
      | ~ r1_orders_2(sK1,sK13(sK0,sK1,X7),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X7)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f153,f180])).

fof(f180,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ r1_orders_2(X1,sK13(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f156,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f98])).
%------------------------------------------------------------------------------
