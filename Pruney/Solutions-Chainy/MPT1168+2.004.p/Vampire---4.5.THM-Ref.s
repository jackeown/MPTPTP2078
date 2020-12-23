%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:14 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   72 (1263 expanded)
%              Number of leaves         :    9 ( 254 expanded)
%              Depth                    :   15
%              Number of atoms          :  392 (10464 expanded)
%              Number of equality atoms :   12 ( 861 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f560,plain,(
    $false ),
    inference(global_subsumption,[],[f553,f547])).

fof(f547,plain,(
    ~ r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f36,f35,f33,f37,f34,f32,f31,f30,f496,f475,f503,f146])).

fof(f146,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ r2_orders_2(X19,sK4(X20,k3_orders_2(X19,X21,X22)),X22)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(sK4(X20,k3_orders_2(X19,X21,X22)),u1_struct_0(X19))
      | ~ m1_subset_1(X22,u1_struct_0(X19))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ v3_orders_2(X19)
      | ~ r2_hidden(sK4(X20,k3_orders_2(X19,X21,X22)),X21)
      | v2_struct_0(X19)
      | ~ r2_hidden(sK4(X20,k3_orders_2(X19,X21,X22)),X20)
      | k3_orders_2(X19,X21,X22) = X20 ) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f503,plain,(
    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK1) ),
    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f32,f27,f496,f500])).

fof(f500,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f475,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_orders_2(X2,X0,X3)
                        & r2_hidden(X1,X2) )
                     => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_orders_2(X2,X0,X3)
                      & r2_hidden(X1,X2) )
                   => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_orders_2)).

fof(f475,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f160,f30,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | X0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(factoring,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f44,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f160,plain,(
    r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f37,f35,f34,f36,f78,f32,f27,f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  | ~ r1_tarski(X2,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  | ~ r1_tarski(X2,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).

fof(f78,plain,(
    r1_tarski(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f35,f34,f33,f37,f36,f29,f27,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f29,plain,(
    m1_orders_2(sK2,sK0,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f496,plain,(
    m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f95,f475,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f95,plain,(
    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f33,f35,f34,f37,f36,f32,f27,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f30,plain,(
    k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f553,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f36,f37,f33,f35,f34,f28,f29,f31,f32,f27,f494,f496,f503,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X4)
      | ~ m1_orders_2(X4,X0,X3)
      | r2_hidden(X1,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

fof(f494,plain,(
    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK3) ),
    inference(unit_resulting_resolution,[],[f320,f475,f46])).

fof(f320,plain,(
    r1_tarski(k3_orders_2(sK0,sK3,sK1),sK3) ),
    inference(duplicate_literal_removal,[],[f318])).

fof(f318,plain,
    ( r1_tarski(k3_orders_2(sK0,sK3,sK1),sK3)
    | r1_tarski(k3_orders_2(sK0,sK3,sK1),sK3) ),
    inference(resolution,[],[f314,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f314,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),X0),sK3)
      | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0) ) ),
    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f32,f27,f313])).

fof(f313,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),X0),sK3)
      | v2_struct_0(sK0)
      | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),X0),sK3)
      | v2_struct_0(sK0)
      | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0)
      | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0) ) ),
    inference(resolution,[],[f104,f117])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),X0),u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0) ) ),
    inference(resolution,[],[f111,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_orders_2(sK0,sK3,sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f95,f50])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(k3_orders_2(X0,X1,X2),X3),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(k3_orders_2(X0,X1,X2),X3),X1)
      | v2_struct_0(X0)
      | r1_tarski(k3_orders_2(X0,X1,X2),X3) ) ),
    inference(resolution,[],[f39,f47])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:01:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (20688)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (20692)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (20697)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (20700)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (20708)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (20705)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (20705)Refutation not found, incomplete strategy% (20705)------------------------------
% 0.22/0.57  % (20705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (20705)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (20705)Memory used [KB]: 10746
% 0.22/0.58  % (20705)Time elapsed: 0.135 s
% 0.22/0.58  % (20705)------------------------------
% 0.22/0.58  % (20705)------------------------------
% 0.22/0.59  % (20690)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.59  % (20684)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (20712)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (20686)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.60  % (20682)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.60  % (20685)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.61  % (20698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.61  % (20683)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.61  % (20710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.61  % (20704)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.61  % (20702)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.61  % (20696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.61  % (20709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.61  % (20711)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.61  % (20703)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.61  % (20701)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.61  % (20706)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.62  % (20693)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.62  % (20695)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.62  % (20707)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.62  % (20689)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.62  % (20694)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.62  % (20699)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.63  % (20687)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.62/0.74  % (20707)Refutation found. Thanks to Tanya!
% 2.62/0.74  % SZS status Theorem for theBenchmark
% 2.90/0.75  % SZS output start Proof for theBenchmark
% 2.90/0.75  fof(f560,plain,(
% 2.90/0.75    $false),
% 2.90/0.75    inference(global_subsumption,[],[f553,f547])).
% 2.90/0.75  fof(f547,plain,(
% 2.90/0.75    ~r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK2)),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f36,f35,f33,f37,f34,f32,f31,f30,f496,f475,f503,f146])).
% 2.90/0.75  fof(f146,plain,(
% 2.90/0.75    ( ! [X21,X19,X22,X20] : (~r2_orders_2(X19,sK4(X20,k3_orders_2(X19,X21,X22)),X22) | ~v4_orders_2(X19) | ~v5_orders_2(X19) | ~l1_orders_2(X19) | ~m1_subset_1(sK4(X20,k3_orders_2(X19,X21,X22)),u1_struct_0(X19)) | ~m1_subset_1(X22,u1_struct_0(X19)) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19))) | ~v3_orders_2(X19) | ~r2_hidden(sK4(X20,k3_orders_2(X19,X21,X22)),X21) | v2_struct_0(X19) | ~r2_hidden(sK4(X20,k3_orders_2(X19,X21,X22)),X20) | k3_orders_2(X19,X21,X22) = X20) )),
% 2.90/0.75    inference(resolution,[],[f40,f45])).
% 2.90/0.75  fof(f45,plain,(
% 2.90/0.75    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 2.90/0.75    inference(cnf_transformation,[],[f21])).
% 2.90/0.75  fof(f21,plain,(
% 2.90/0.75    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.90/0.75    inference(ennf_transformation,[],[f2])).
% 2.90/0.75  fof(f2,axiom,(
% 2.90/0.75    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 2.90/0.75  fof(f40,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | v2_struct_0(X0)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f14])).
% 2.90/0.75  fof(f14,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.90/0.75    inference(flattening,[],[f13])).
% 2.90/0.75  fof(f13,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f5])).
% 2.90/0.75  fof(f5,axiom,(
% 2.90/0.75    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 2.90/0.75  fof(f503,plain,(
% 2.90/0.75    r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK1)),
% 2.90/0.75    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f32,f27,f496,f500])).
% 2.90/0.75  fof(f500,plain,(
% 2.90/0.75    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK1) | v2_struct_0(sK0)),
% 2.90/0.75    inference(resolution,[],[f475,f38])).
% 2.90/0.75  fof(f38,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f14])).
% 2.90/0.75  fof(f27,plain,(
% 2.90/0.75    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f12,plain,(
% 2.90/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.90/0.75    inference(flattening,[],[f11])).
% 2.90/0.75  fof(f11,plain,(
% 2.90/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & (m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f10])).
% 2.90/0.75  fof(f10,negated_conjecture,(
% 2.90/0.75    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 2.90/0.75    inference(negated_conjecture,[],[f9])).
% 2.90/0.75  fof(f9,conjecture,(
% 2.90/0.75    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_orders_2)).
% 2.90/0.75  fof(f475,plain,(
% 2.90/0.75    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),k3_orders_2(sK0,sK3,sK1))),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f160,f30,f76])).
% 2.90/0.75  fof(f76,plain,(
% 2.90/0.75    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | X0 = X1 | ~r1_tarski(X1,X0)) )),
% 2.90/0.75    inference(factoring,[],[f61])).
% 2.90/0.75  fof(f61,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),X2) | X0 = X1 | r2_hidden(sK4(X0,X1),X0) | ~r1_tarski(X1,X2)) )),
% 2.90/0.75    inference(resolution,[],[f44,f46])).
% 2.90/0.75  fof(f46,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f22])).
% 2.90/0.75  fof(f22,plain,(
% 2.90/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f1])).
% 2.90/0.75  fof(f1,axiom,(
% 2.90/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.90/0.75  fof(f44,plain,(
% 2.90/0.75    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 2.90/0.75    inference(cnf_transformation,[],[f21])).
% 2.90/0.75  fof(f160,plain,(
% 2.90/0.75    r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1))),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f33,f37,f35,f34,f36,f78,f32,f27,f31,f42])).
% 2.90/0.75  fof(f42,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X3) | v2_struct_0(X0)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f18])).
% 2.90/0.75  fof(f18,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) | ~r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.90/0.75    inference(flattening,[],[f17])).
% 2.90/0.75  fof(f17,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) | ~r1_tarski(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f6])).
% 2.90/0.75  fof(f6,axiom,(
% 2.90/0.75    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X3) => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)))))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).
% 2.90/0.75  fof(f78,plain,(
% 2.90/0.75    r1_tarski(sK2,sK3)),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f35,f34,f33,f37,f36,f29,f27,f43])).
% 2.90/0.75  fof(f43,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f20])).
% 2.90/0.75  fof(f20,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.90/0.75    inference(flattening,[],[f19])).
% 2.90/0.75  fof(f19,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f7])).
% 2.90/0.75  fof(f7,axiom,(
% 2.90/0.75    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 2.90/0.75  fof(f29,plain,(
% 2.90/0.75    m1_orders_2(sK2,sK0,sK3)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f496,plain,(
% 2.90/0.75    m1_subset_1(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),u1_struct_0(sK0))),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f95,f475,f50])).
% 2.90/0.75  fof(f50,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f26])).
% 2.90/0.75  fof(f26,plain,(
% 2.90/0.75    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.90/0.75    inference(flattening,[],[f25])).
% 2.90/0.75  fof(f25,plain,(
% 2.90/0.75    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.90/0.75    inference(ennf_transformation,[],[f3])).
% 2.90/0.75  fof(f3,axiom,(
% 2.90/0.75    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.90/0.75  fof(f95,plain,(
% 2.90/0.75    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f33,f35,f34,f37,f36,f32,f27,f49])).
% 2.90/0.75  fof(f49,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f24])).
% 2.90/0.75  fof(f24,plain,(
% 2.90/0.75    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.90/0.75    inference(flattening,[],[f23])).
% 2.90/0.75  fof(f23,plain,(
% 2.90/0.75    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f4])).
% 2.90/0.75  fof(f4,axiom,(
% 2.90/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 2.90/0.75  fof(f30,plain,(
% 2.90/0.75    k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f31,plain,(
% 2.90/0.75    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f32,plain,(
% 2.90/0.75    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f34,plain,(
% 2.90/0.75    v3_orders_2(sK0)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f37,plain,(
% 2.90/0.75    l1_orders_2(sK0)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f33,plain,(
% 2.90/0.75    ~v2_struct_0(sK0)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f35,plain,(
% 2.90/0.75    v4_orders_2(sK0)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f36,plain,(
% 2.90/0.75    v5_orders_2(sK0)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  fof(f553,plain,(
% 2.90/0.75    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK2)),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f36,f37,f33,f35,f34,f28,f29,f31,f32,f27,f494,f496,f503,f41])).
% 2.90/0.75  fof(f41,plain,(
% 2.90/0.75    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X4) | ~m1_orders_2(X4,X0,X3) | r2_hidden(X1,X4)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f16])).
% 2.90/0.75  fof(f16,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.90/0.75    inference(flattening,[],[f15])).
% 2.90/0.75  fof(f15,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X1,X4) | (~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f8])).
% 2.90/0.75  fof(f8,axiom,(
% 2.90/0.75    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).
% 2.90/0.75  fof(f494,plain,(
% 2.90/0.75    r2_hidden(sK4(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK2,sK1)),sK3)),
% 2.90/0.75    inference(unit_resulting_resolution,[],[f320,f475,f46])).
% 2.90/0.75  fof(f320,plain,(
% 2.90/0.75    r1_tarski(k3_orders_2(sK0,sK3,sK1),sK3)),
% 2.90/0.75    inference(duplicate_literal_removal,[],[f318])).
% 2.90/0.75  fof(f318,plain,(
% 2.90/0.75    r1_tarski(k3_orders_2(sK0,sK3,sK1),sK3) | r1_tarski(k3_orders_2(sK0,sK3,sK1),sK3)),
% 2.90/0.75    inference(resolution,[],[f314,f48])).
% 2.90/0.75  fof(f48,plain,(
% 2.90/0.75    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f22])).
% 2.90/0.75  fof(f314,plain,(
% 2.90/0.75    ( ! [X0] : (r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),X0),sK3) | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0)) )),
% 2.90/0.75    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f32,f27,f313])).
% 2.90/0.75  fof(f313,plain,(
% 2.90/0.75    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),X0),sK3) | v2_struct_0(sK0) | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0)) )),
% 2.90/0.75    inference(duplicate_literal_removal,[],[f308])).
% 2.90/0.75  fof(f308,plain,(
% 2.90/0.75    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),X0),sK3) | v2_struct_0(sK0) | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0) | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0)) )),
% 2.90/0.75    inference(resolution,[],[f104,f117])).
% 2.90/0.75  fof(f117,plain,(
% 2.90/0.75    ( ! [X0] : (m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),X0),u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,sK1),X0)) )),
% 2.90/0.75    inference(resolution,[],[f111,f47])).
% 2.90/0.75  fof(f47,plain,(
% 2.90/0.75    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f22])).
% 2.90/0.75  fof(f111,plain,(
% 2.90/0.75    ( ! [X1] : (~r2_hidden(X1,k3_orders_2(sK0,sK3,sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.90/0.75    inference(resolution,[],[f95,f50])).
% 2.90/0.75  fof(f104,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(k3_orders_2(X0,X1,X2),X3),u1_struct_0(X0)) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK5(k3_orders_2(X0,X1,X2),X3),X1) | v2_struct_0(X0) | r1_tarski(k3_orders_2(X0,X1,X2),X3)) )),
% 2.90/0.75    inference(resolution,[],[f39,f47])).
% 2.90/0.75  fof(f39,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | v2_struct_0(X0)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f14])).
% 2.90/0.75  fof(f28,plain,(
% 2.90/0.75    r2_hidden(sK1,sK2)),
% 2.90/0.75    inference(cnf_transformation,[],[f12])).
% 2.90/0.75  % SZS output end Proof for theBenchmark
% 2.90/0.75  % (20707)------------------------------
% 2.90/0.75  % (20707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.75  % (20707)Termination reason: Refutation
% 2.90/0.75  
% 2.90/0.75  % (20707)Memory used [KB]: 7291
% 2.90/0.75  % (20707)Time elapsed: 0.311 s
% 2.90/0.75  % (20707)------------------------------
% 2.90/0.75  % (20707)------------------------------
% 2.90/0.75  % (20681)Success in time 0.376 s
%------------------------------------------------------------------------------
