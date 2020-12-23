%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (1465 expanded)
%              Number of leaves         :   10 ( 692 expanded)
%              Depth                    :   10
%              Number of atoms          :  315 (13501 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f34,f31,f32,f68,f50,f72,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X3)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

fof(f72,plain,(
    ~ r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f32,f33,f69,f50,f52,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f52,plain,(
    ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f35,f45,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK4(X0,X1,X2),X2)
            & r2_hidden(sK4(X0,X1,X2),X1)
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f45,plain,(
    m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f32,f33,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f35,plain,(
    ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
    & r2_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                    & r2_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(sK0,X3,X1),k3_orders_2(sK0,X3,X2))
                  & r2_orders_2(sK0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k3_orders_2(sK0,X3,X1),k3_orders_2(sK0,X3,X2))
                & r2_orders_2(sK0,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,X2))
              & r2_orders_2(sK0,sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,X2))
            & r2_orders_2(sK0,sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,sK2))
          & r2_orders_2(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,sK2))
        & r2_orders_2(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
      & r2_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( r2_orders_2(X0,X1,X2)
                     => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_orders_2(X0,X1,X2)
                   => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

fof(f44,plain,(
    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f31,f33,f43])).

fof(f69,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f31,f33,f50,f51,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f44,f35,f45,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f35,f45,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f31,f33,f50,f51,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:09:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.43  % (29874)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.43  % (29874)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f28,f29,f30,f34,f31,f32,f68,f50,f72,f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 0.20/0.44    inference(flattening,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | (~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)) => r2_orders_2(X0,X1,X3))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ~r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f32,f33,f69,f50,f52,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK2))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f44,f35,f45,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(flattening,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f32,f33,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ~r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    (((~r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f20,f19,f18,f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) & r2_orders_2(X0,X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(sK0,X3,X1),k3_orders_2(sK0,X3,X2)) & r2_orders_2(sK0,X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(sK0,X3,X1),k3_orders_2(sK0,X3,X2)) & r2_orders_2(sK0,X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,X2)) & r2_orders_2(sK0,sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,X2)) & r2_orders_2(sK0,sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,sK2)) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ? [X3] : (~r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,sK2)) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) & r2_orders_2(X0,X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f7])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) & r2_orders_2(X0,X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_orders_2(X0,X1,X2) => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)))))))),
% 0.20/0.44    inference(negated_conjecture,[],[f5])).
% 0.20/0.44  fof(f5,conjecture,(
% 0.20/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_orders_2(X0,X1,X2) => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f31,f33,f43])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f31,f33,f50,f51,f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f44,f35,f45,f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    v3_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ~v2_struct_0(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f44,f35,f45,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f31,f33,f50,f51,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    l1_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    v5_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    v4_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (29874)------------------------------
% 0.20/0.44  % (29874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (29874)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (29874)Memory used [KB]: 1023
% 0.20/0.44  % (29874)Time elapsed: 0.048 s
% 0.20/0.44  % (29874)------------------------------
% 0.20/0.44  % (29874)------------------------------
% 0.20/0.44  % (29868)Success in time 0.094 s
%------------------------------------------------------------------------------
