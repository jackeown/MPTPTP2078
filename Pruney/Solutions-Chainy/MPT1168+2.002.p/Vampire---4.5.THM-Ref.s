%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:13 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  133 (1216 expanded)
%              Number of leaves         :   13 ( 490 expanded)
%              Depth                    :   30
%              Number of atoms          :  793 (11505 expanded)
%              Number of equality atoms :   24 (1155 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f550,plain,(
    $false ),
    inference(subsumption_resolution,[],[f541,f46])).

fof(f46,plain,(
    k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1)
    & m1_orders_2(sK2,sK0,sK3)
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1)
                  & m1_orders_2(X2,sK0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1)
                & m1_orders_2(X2,sK0,X3)
                & r2_hidden(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1)
              & m1_orders_2(X2,sK0,X3)
              & r2_hidden(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1)
            & m1_orders_2(X2,sK0,X3)
            & r2_hidden(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1)
          & m1_orders_2(sK2,sK0,X3)
          & r2_hidden(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1)
        & m1_orders_2(sK2,sK0,X3)
        & r2_hidden(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1)
      & m1_orders_2(sK2,sK0,sK3)
      & r2_hidden(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_orders_2)).

fof(f541,plain,(
    k3_orders_2(sK0,sK2,sK1) = k3_orders_2(sK0,sK3,sK1) ),
    inference(resolution,[],[f540,f44])).

fof(f44,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f540,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k3_orders_2(sK0,sK2,X0) = k3_orders_2(sK0,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f537,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f59,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f537,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_orders_2(sK0,sK2,X0) = k3_orders_2(sK0,sK3,X0) ) ),
    inference(resolution,[],[f524,f406])).

fof(f406,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_orders_2(sK0,sK3,X2),k3_orders_2(sK0,sK2,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k3_orders_2(sK0,sK2,X2) = k3_orders_2(sK0,sK3,X2) ) ),
    inference(resolution,[],[f402,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f402,plain,(
    ! [X0] :
      ( r1_tarski(k3_orders_2(sK0,sK2,X0),k3_orders_2(sK0,sK3,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f391])).

fof(f391,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK2,X0),k3_orders_2(sK0,sK3,X0))
      | r1_tarski(k3_orders_2(sK0,sK2,X0),k3_orders_2(sK0,sK3,X0)) ) ),
    inference(resolution,[],[f389,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f389,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),k3_orders_2(sK0,sK3,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK2,X6),X7) ) ),
    inference(subsumption_resolution,[],[f383,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK2,X0),X1),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK2,X0),X1) ) ),
    inference(resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(sK0,sK2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f105,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,(
    ! [X0] :
      ( r1_tarski(k3_orders_2(sK0,sK2,X0),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK2,X0),sK3)
      | r1_tarski(k3_orders_2(sK0,sK2,X0),sK3) ) ),
    inference(resolution,[],[f95,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK3),sK2)
      | r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f75,f57])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f74,f55])).

fof(f74,plain,(
    r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f73,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    m1_orders_2(sK2,sK0,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f37,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f38,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f39,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X2,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f95,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK2,X4),X5),sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK2,X4),X5) ) ),
    inference(resolution,[],[f93,f42])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),X0)
      | r1_tarski(k3_orders_2(sK0,X0,X1),X2) ) ),
    inference(resolution,[],[f92,f56])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f91,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_orders_2(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,k3_orders_2(sK0,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f83,f37])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,k3_orders_2(sK0,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,k3_orders_2(sK0,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f81,f39])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,k3_orders_2(sK0,X0,X1)) ) ),
    inference(resolution,[],[f77,f40])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,k3_orders_2(X1,X2,X0)) ) ),
    inference(resolution,[],[f58,f59])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f39])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f383,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),k3_orders_2(sK0,sK3,X6))
      | ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),sK3)
      | r1_tarski(k3_orders_2(sK0,sK2,X6),X7) ) ),
    inference(resolution,[],[f255,f43])).

fof(f255,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),k3_orders_2(sK0,X5,X6))
      | ~ r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),X5)
      | r1_tarski(k3_orders_2(sK0,sK2,X6),X7) ) ),
    inference(resolution,[],[f133,f42])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),k3_orders_2(sK0,X3,X1))
      | ~ r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),X3)
      | r1_tarski(k3_orders_2(sK0,X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),k3_orders_2(sK0,X3,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k3_orders_2(sK0,X0,X1),X2) ) ),
    inference(resolution,[],[f131,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,sK4(k3_orders_2(sK0,X0,X1),X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k3_orders_2(sK0,X0,X1),X2) ) ),
    inference(resolution,[],[f122,f56])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f121,f85])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f120,f36])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f37])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,X2)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f38])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,X2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,X2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f40])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f130,f59])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK0,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f129,f36])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK0,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f37])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK0,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f38])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK0,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f39])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_orders_2(sK0,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f524,plain,(
    ! [X0] :
      ( r1_tarski(k3_orders_2(sK0,sK3,X0),k3_orders_2(sK0,sK2,X0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,(
    ! [X0] :
      ( r1_tarski(k3_orders_2(sK0,sK3,X0),k3_orders_2(sK0,sK2,X0))
      | ~ r2_hidden(X0,sK2)
      | r1_tarski(k3_orders_2(sK0,sK3,X0),k3_orders_2(sK0,sK2,X0)) ) ),
    inference(resolution,[],[f516,f57])).

fof(f516,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),k3_orders_2(sK0,sK2,X0))
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f515,f66])).

fof(f515,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),k3_orders_2(sK0,sK2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),k3_orders_2(sK0,sK2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)
      | ~ r2_hidden(X0,sK2)
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) ) ),
    inference(resolution,[],[f451,f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),sK2)
      | ~ r2_hidden(X0,sK2)
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) ) ),
    inference(subsumption_resolution,[],[f217,f66])).

fof(f217,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),sK2)
      | ~ r2_hidden(X0,sK2)
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),sK2)
      | ~ r2_hidden(X0,sK2)
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) ) ),
    inference(resolution,[],[f206,f96])).

fof(f96,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK4(k3_orders_2(sK0,sK3,X6),X7),sK3)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK3,X6),X7) ) ),
    inference(resolution,[],[f93,f43])).

fof(f206,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,sK3,X6),X7),sK3)
      | r2_hidden(sK4(k3_orders_2(sK0,sK3,X6),X7),sK2)
      | ~ r2_hidden(X6,sK2)
      | r1_tarski(k3_orders_2(sK0,sK3,X6),X7) ) ),
    inference(resolution,[],[f203,f43])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK2)
      | ~ r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK3)
      | r1_tarski(k3_orders_2(sK0,X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f201,f66])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK3)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k3_orders_2(sK0,X0,X1),X2) ) ),
    inference(resolution,[],[f200,f125])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f199,f43])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f198,f42])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f186,f45])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,X0) ) ),
    inference(subsumption_resolution,[],[f185,f59])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,X0) ) ),
    inference(subsumption_resolution,[],[f184,f59])).

fof(f184,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,X0) ) ),
    inference(subsumption_resolution,[],[f183,f36])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f37])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f38])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f39])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f40])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X4,X0,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,X4)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).

fof(f451,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,sK3,X4),X5),sK2)
      | r2_hidden(sK4(k3_orders_2(sK0,sK3,X4),X5),k3_orders_2(sK0,sK2,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,sK3,X4),X5) ) ),
    inference(resolution,[],[f256,f42])).

fof(f256,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(sK4(k3_orders_2(sK0,sK3,X9),X10),k3_orders_2(sK0,X8,X9))
      | ~ r2_hidden(sK4(k3_orders_2(sK0,sK3,X9),X10),X8)
      | r1_tarski(k3_orders_2(sK0,sK3,X9),X10) ) ),
    inference(resolution,[],[f133,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (10756)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (10764)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (10761)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (10762)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10765)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (10773)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (10778)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (10773)Refutation not found, incomplete strategy% (10773)------------------------------
% 0.21/0.54  % (10773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10779)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (10773)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10773)Memory used [KB]: 10746
% 0.21/0.54  % (10773)Time elapsed: 0.119 s
% 0.21/0.54  % (10773)------------------------------
% 0.21/0.54  % (10773)------------------------------
% 0.21/0.54  % (10763)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10785)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (10760)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (10757)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (10782)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (10771)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (10758)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (10758)Refutation not found, incomplete strategy% (10758)------------------------------
% 0.21/0.55  % (10758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10758)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10758)Memory used [KB]: 10746
% 0.21/0.55  % (10758)Time elapsed: 0.136 s
% 0.21/0.55  % (10758)------------------------------
% 0.21/0.55  % (10758)------------------------------
% 0.21/0.55  % (10770)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (10783)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (10774)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (10784)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (10780)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (10772)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (10776)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (10766)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (10775)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (10778)Refutation not found, incomplete strategy% (10778)------------------------------
% 0.21/0.56  % (10778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10778)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10778)Memory used [KB]: 10746
% 0.21/0.56  % (10778)Time elapsed: 0.153 s
% 0.21/0.56  % (10778)------------------------------
% 0.21/0.56  % (10778)------------------------------
% 0.21/0.56  % (10781)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (10768)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (10767)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (10759)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (10777)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.59  % (10769)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.77/0.62  % (10763)Refutation found. Thanks to Tanya!
% 1.77/0.62  % SZS status Theorem for theBenchmark
% 1.77/0.62  % SZS output start Proof for theBenchmark
% 1.77/0.62  fof(f550,plain,(
% 1.77/0.62    $false),
% 1.77/0.62    inference(subsumption_resolution,[],[f541,f46])).
% 1.77/0.62  fof(f46,plain,(
% 1.77/0.62    k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1)),
% 1.77/0.62    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f27,plain,(
% 1.77/0.63    (((k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1) & m1_orders_2(sK2,sK0,sK3) & r2_hidden(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.77/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f26,f25,f24,f23])).
% 1.77/0.63  fof(f23,plain,(
% 1.77/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1) & m1_orders_2(X2,sK0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.77/0.63    introduced(choice_axiom,[])).
% 1.77/0.63  fof(f24,plain,(
% 1.77/0.63    ? [X1] : (? [X2] : (? [X3] : (k3_orders_2(sK0,X2,X1) != k3_orders_2(sK0,X3,X1) & m1_orders_2(X2,sK0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1) & m1_orders_2(X2,sK0,X3) & r2_hidden(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.77/0.63    introduced(choice_axiom,[])).
% 1.77/0.63  fof(f25,plain,(
% 1.77/0.63    ? [X2] : (? [X3] : (k3_orders_2(sK0,X2,sK1) != k3_orders_2(sK0,X3,sK1) & m1_orders_2(X2,sK0,X3) & r2_hidden(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1) & m1_orders_2(sK2,sK0,X3) & r2_hidden(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.77/0.63    introduced(choice_axiom,[])).
% 1.77/0.63  fof(f26,plain,(
% 1.77/0.63    ? [X3] : (k3_orders_2(sK0,X3,sK1) != k3_orders_2(sK0,sK2,sK1) & m1_orders_2(sK2,sK0,X3) & r2_hidden(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (k3_orders_2(sK0,sK2,sK1) != k3_orders_2(sK0,sK3,sK1) & m1_orders_2(sK2,sK0,sK3) & r2_hidden(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.77/0.63    introduced(choice_axiom,[])).
% 1.77/0.63  fof(f11,plain,(
% 1.77/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.77/0.63    inference(flattening,[],[f10])).
% 1.77/0.63  fof(f10,plain,(
% 1.77/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & (m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.77/0.63    inference(ennf_transformation,[],[f9])).
% 1.77/0.63  fof(f9,negated_conjecture,(
% 1.77/0.63    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 1.77/0.63    inference(negated_conjecture,[],[f8])).
% 1.77/0.63  fof(f8,conjecture,(
% 1.77/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_orders_2)).
% 1.77/0.63  fof(f541,plain,(
% 1.77/0.63    k3_orders_2(sK0,sK2,sK1) = k3_orders_2(sK0,sK3,sK1)),
% 1.77/0.63    inference(resolution,[],[f540,f44])).
% 1.77/0.63  fof(f44,plain,(
% 1.77/0.63    r2_hidden(sK1,sK2)),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f540,plain,(
% 1.77/0.63    ( ! [X0] : (~r2_hidden(X0,sK2) | k3_orders_2(sK0,sK2,X0) = k3_orders_2(sK0,sK3,X0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f537,f66])).
% 1.77/0.63  fof(f66,plain,(
% 1.77/0.63    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2)) )),
% 1.77/0.63    inference(resolution,[],[f59,f42])).
% 1.77/0.63  fof(f42,plain,(
% 1.77/0.63    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f59,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f22])).
% 1.77/0.63  fof(f22,plain,(
% 1.77/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.77/0.63    inference(flattening,[],[f21])).
% 1.77/0.63  fof(f21,plain,(
% 1.77/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.77/0.63    inference(ennf_transformation,[],[f3])).
% 1.77/0.63  fof(f3,axiom,(
% 1.77/0.63    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.77/0.63  fof(f537,plain,(
% 1.77/0.63    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_orders_2(sK0,sK2,X0) = k3_orders_2(sK0,sK3,X0)) )),
% 1.77/0.63    inference(resolution,[],[f524,f406])).
% 1.77/0.63  fof(f406,plain,(
% 1.77/0.63    ( ! [X2] : (~r1_tarski(k3_orders_2(sK0,sK3,X2),k3_orders_2(sK0,sK2,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k3_orders_2(sK0,sK2,X2) = k3_orders_2(sK0,sK3,X2)) )),
% 1.77/0.63    inference(resolution,[],[f402,f54])).
% 1.77/0.63  fof(f54,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.77/0.63    inference(cnf_transformation,[],[f31])).
% 1.77/0.63  fof(f31,plain,(
% 1.77/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/0.63    inference(flattening,[],[f30])).
% 1.77/0.63  fof(f30,plain,(
% 1.77/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/0.63    inference(nnf_transformation,[],[f2])).
% 1.77/0.63  fof(f2,axiom,(
% 1.77/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.77/0.63  fof(f402,plain,(
% 1.77/0.63    ( ! [X0] : (r1_tarski(k3_orders_2(sK0,sK2,X0),k3_orders_2(sK0,sK3,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.77/0.63    inference(duplicate_literal_removal,[],[f391])).
% 1.77/0.63  fof(f391,plain,(
% 1.77/0.63    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK2,X0),k3_orders_2(sK0,sK3,X0)) | r1_tarski(k3_orders_2(sK0,sK2,X0),k3_orders_2(sK0,sK3,X0))) )),
% 1.77/0.63    inference(resolution,[],[f389,f57])).
% 1.77/0.63  fof(f57,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f35])).
% 1.77/0.63  fof(f35,plain,(
% 1.77/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.77/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.77/0.63  fof(f34,plain,(
% 1.77/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.77/0.63    introduced(choice_axiom,[])).
% 1.77/0.63  fof(f33,plain,(
% 1.77/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.77/0.63    inference(rectify,[],[f32])).
% 1.77/0.63  fof(f32,plain,(
% 1.77/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.77/0.63    inference(nnf_transformation,[],[f18])).
% 1.77/0.63  fof(f18,plain,(
% 1.77/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.77/0.63    inference(ennf_transformation,[],[f1])).
% 1.77/0.63  fof(f1,axiom,(
% 1.77/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.77/0.63  fof(f389,plain,(
% 1.77/0.63    ( ! [X6,X7] : (r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),k3_orders_2(sK0,sK3,X6)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK2,X6),X7)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f383,f111])).
% 1.77/0.63  fof(f111,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(k3_orders_2(sK0,sK2,X0),X1),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK2,X0),X1)) )),
% 1.77/0.63    inference(resolution,[],[f108,f56])).
% 1.77/0.63  fof(f56,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f35])).
% 1.77/0.63  fof(f108,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~r2_hidden(X1,k3_orders_2(sK0,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK3)) )),
% 1.77/0.63    inference(resolution,[],[f105,f55])).
% 1.77/0.63  fof(f55,plain,(
% 1.77/0.63    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f35])).
% 1.77/0.63  fof(f105,plain,(
% 1.77/0.63    ( ! [X0] : (r1_tarski(k3_orders_2(sK0,sK2,X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.77/0.63    inference(duplicate_literal_removal,[],[f102])).
% 1.77/0.63  fof(f102,plain,(
% 1.77/0.63    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK2,X0),sK3) | r1_tarski(k3_orders_2(sK0,sK2,X0),sK3)) )),
% 1.77/0.63    inference(resolution,[],[f95,f78])).
% 1.77/0.63  fof(f78,plain,(
% 1.77/0.63    ( ! [X0] : (~r2_hidden(sK4(X0,sK3),sK2) | r1_tarski(X0,sK3)) )),
% 1.77/0.63    inference(resolution,[],[f75,f57])).
% 1.77/0.63  fof(f75,plain,(
% 1.77/0.63    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK2)) )),
% 1.77/0.63    inference(resolution,[],[f74,f55])).
% 1.77/0.63  fof(f74,plain,(
% 1.77/0.63    r1_tarski(sK2,sK3)),
% 1.77/0.63    inference(subsumption_resolution,[],[f73,f43])).
% 1.77/0.63  fof(f43,plain,(
% 1.77/0.63    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f73,plain,(
% 1.77/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 1.77/0.63    inference(resolution,[],[f72,f45])).
% 1.77/0.63  fof(f45,plain,(
% 1.77/0.63    m1_orders_2(sK2,sK0,sK3)),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f72,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f71,f36])).
% 1.77/0.63  fof(f36,plain,(
% 1.77/0.63    ~v2_struct_0(sK0)),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f71,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f70,f37])).
% 1.77/0.63  fof(f37,plain,(
% 1.77/0.63    v3_orders_2(sK0)),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f70,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f69,f38])).
% 1.77/0.63  fof(f38,plain,(
% 1.77/0.63    v4_orders_2(sK0)),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f69,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f68,f39])).
% 1.77/0.63  fof(f39,plain,(
% 1.77/0.63    v5_orders_2(sK0)),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f68,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(resolution,[],[f51,f40])).
% 1.77/0.63  fof(f40,plain,(
% 1.77/0.63    l1_orders_2(sK0)),
% 1.77/0.63    inference(cnf_transformation,[],[f27])).
% 1.77/0.63  fof(f51,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X2,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f17])).
% 1.77/0.63  fof(f17,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.77/0.63    inference(flattening,[],[f16])).
% 1.77/0.63  fof(f16,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.77/0.63    inference(ennf_transformation,[],[f6])).
% 1.77/0.63  fof(f6,axiom,(
% 1.77/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 1.77/0.63  fof(f95,plain,(
% 1.77/0.63    ( ! [X4,X5] : (r2_hidden(sK4(k3_orders_2(sK0,sK2,X4),X5),sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK2,X4),X5)) )),
% 1.77/0.63    inference(resolution,[],[f93,f42])).
% 1.77/0.63  fof(f93,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),X0) | r1_tarski(k3_orders_2(sK0,X0,X1),X2)) )),
% 1.77/0.63    inference(resolution,[],[f92,f56])).
% 1.77/0.63  fof(f92,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X0,X1)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f91,f85])).
% 1.77/0.63  fof(f85,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_orders_2(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f84,f36])).
% 1.77/0.63  fof(f84,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k3_orders_2(sK0,X0,X1))) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f83,f37])).
% 1.77/0.63  fof(f83,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k3_orders_2(sK0,X0,X1))) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f82,f38])).
% 1.77/0.63  fof(f82,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k3_orders_2(sK0,X0,X1))) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f81,f39])).
% 1.77/0.63  fof(f81,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k3_orders_2(sK0,X0,X1))) )),
% 1.77/0.63    inference(resolution,[],[f77,f40])).
% 1.77/0.63  fof(f77,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(X3,k3_orders_2(X1,X2,X0))) )),
% 1.77/0.63    inference(resolution,[],[f58,f59])).
% 1.77/0.63  fof(f58,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f20])).
% 1.77/0.63  fof(f20,plain,(
% 1.77/0.63    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.77/0.63    inference(flattening,[],[f19])).
% 1.77/0.63  fof(f19,plain,(
% 1.77/0.63    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.77/0.63    inference(ennf_transformation,[],[f4])).
% 1.77/0.63  fof(f4,axiom,(
% 1.77/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 1.77/0.63  fof(f91,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f90,f36])).
% 1.77/0.63  fof(f90,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f89,f37])).
% 1.77/0.63  fof(f89,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f88,f38])).
% 1.77/0.63  fof(f88,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f87,f39])).
% 1.77/0.63  fof(f87,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(resolution,[],[f48,f40])).
% 1.77/0.63  fof(f48,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f29])).
% 1.77/0.63  fof(f29,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.77/0.63    inference(flattening,[],[f28])).
% 1.77/0.63  fof(f28,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.77/0.63    inference(nnf_transformation,[],[f13])).
% 1.77/0.63  fof(f13,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.77/0.63    inference(flattening,[],[f12])).
% 1.77/0.63  fof(f12,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.77/0.63    inference(ennf_transformation,[],[f5])).
% 1.77/0.63  fof(f5,axiom,(
% 1.77/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 1.77/0.63  fof(f383,plain,(
% 1.77/0.63    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK0)) | r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),k3_orders_2(sK0,sK3,X6)) | ~r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),sK3) | r1_tarski(k3_orders_2(sK0,sK2,X6),X7)) )),
% 1.77/0.63    inference(resolution,[],[f255,f43])).
% 1.77/0.63  fof(f255,plain,(
% 1.77/0.63    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),k3_orders_2(sK0,X5,X6)) | ~r2_hidden(sK4(k3_orders_2(sK0,sK2,X6),X7),X5) | r1_tarski(k3_orders_2(sK0,sK2,X6),X7)) )),
% 1.77/0.63    inference(resolution,[],[f133,f42])).
% 1.77/0.63  fof(f133,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),k3_orders_2(sK0,X3,X1)) | ~r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),X3) | r1_tarski(k3_orders_2(sK0,X0,X1),X2)) )),
% 1.77/0.63    inference(duplicate_literal_removal,[],[f132])).
% 1.77/0.63  fof(f132,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),k3_orders_2(sK0,X3,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_orders_2(sK0,X0,X1),X2)) )),
% 1.77/0.63    inference(resolution,[],[f131,f125])).
% 1.77/0.63  fof(f125,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (r2_orders_2(sK0,sK4(k3_orders_2(sK0,X0,X1),X2),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_orders_2(sK0,X0,X1),X2)) )),
% 1.77/0.63    inference(resolution,[],[f122,f56])).
% 1.77/0.63  fof(f122,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X2)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f121,f85])).
% 1.77/0.63  fof(f121,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X2)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f120,f36])).
% 1.77/0.63  fof(f120,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X2) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f119,f37])).
% 1.77/0.63  fof(f119,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f118,f38])).
% 1.77/0.63  fof(f118,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f117,f39])).
% 1.77/0.63  fof(f117,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(resolution,[],[f47,f40])).
% 1.77/0.63  fof(f47,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_orders_2(X0,X1,X2) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f29])).
% 1.77/0.63  fof(f131,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_orders_2(sK0,X0,X2) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,X1,X2))) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f130,f59])).
% 1.77/0.63  fof(f130,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,X1,X2))) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f129,f36])).
% 1.77/0.63  fof(f129,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f128,f37])).
% 1.77/0.63  fof(f128,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f127,f38])).
% 1.77/0.63  fof(f127,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f126,f39])).
% 1.77/0.63  fof(f126,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(resolution,[],[f49,f40])).
% 1.77/0.63  fof(f49,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f29])).
% 1.77/0.63  fof(f524,plain,(
% 1.77/0.63    ( ! [X0] : (r1_tarski(k3_orders_2(sK0,sK3,X0),k3_orders_2(sK0,sK2,X0)) | ~r2_hidden(X0,sK2)) )),
% 1.77/0.63    inference(duplicate_literal_removal,[],[f517])).
% 1.77/0.63  fof(f517,plain,(
% 1.77/0.63    ( ! [X0] : (r1_tarski(k3_orders_2(sK0,sK3,X0),k3_orders_2(sK0,sK2,X0)) | ~r2_hidden(X0,sK2) | r1_tarski(k3_orders_2(sK0,sK3,X0),k3_orders_2(sK0,sK2,X0))) )),
% 1.77/0.63    inference(resolution,[],[f516,f57])).
% 1.77/0.63  fof(f516,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),k3_orders_2(sK0,sK2,X0)) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) | ~r2_hidden(X0,sK2)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f515,f66])).
% 1.77/0.63  fof(f515,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),k3_orders_2(sK0,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) | ~r2_hidden(X0,sK2)) )),
% 1.77/0.63    inference(duplicate_literal_removal,[],[f514])).
% 1.77/0.63  fof(f514,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),k3_orders_2(sK0,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) | ~r2_hidden(X0,sK2) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)) )),
% 1.77/0.63    inference(resolution,[],[f451,f218])).
% 1.77/0.63  fof(f218,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),sK2) | ~r2_hidden(X0,sK2) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f217,f66])).
% 1.77/0.63  fof(f217,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),sK2) | ~r2_hidden(X0,sK2) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.77/0.63    inference(duplicate_literal_removal,[],[f215])).
% 1.77/0.63  fof(f215,plain,(
% 1.77/0.63    ( ! [X0,X1] : (r2_hidden(sK4(k3_orders_2(sK0,sK3,X0),X1),sK2) | ~r2_hidden(X0,sK2) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X0),X1)) )),
% 1.77/0.63    inference(resolution,[],[f206,f96])).
% 1.77/0.63  fof(f96,plain,(
% 1.77/0.63    ( ! [X6,X7] : (r2_hidden(sK4(k3_orders_2(sK0,sK3,X6),X7),sK3) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X6),X7)) )),
% 1.77/0.63    inference(resolution,[],[f93,f43])).
% 1.77/0.63  fof(f206,plain,(
% 1.77/0.63    ( ! [X6,X7] : (~r2_hidden(sK4(k3_orders_2(sK0,sK3,X6),X7),sK3) | r2_hidden(sK4(k3_orders_2(sK0,sK3,X6),X7),sK2) | ~r2_hidden(X6,sK2) | r1_tarski(k3_orders_2(sK0,sK3,X6),X7)) )),
% 1.77/0.63    inference(resolution,[],[f203,f43])).
% 1.77/0.63  fof(f203,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK2) | ~r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK3) | r1_tarski(k3_orders_2(sK0,X0,X1),X2)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f201,f66])).
% 1.77/0.63  fof(f201,plain,(
% 1.77/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK3) | ~r2_hidden(X1,sK2) | r2_hidden(sK4(k3_orders_2(sK0,X0,X1),X2),sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_orders_2(sK0,X0,X1),X2)) )),
% 1.77/0.63    inference(resolution,[],[f200,f125])).
% 1.77/0.63  fof(f200,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~r2_orders_2(sK0,X1,X0) | ~r2_hidden(X1,sK3) | ~r2_hidden(X0,sK2) | r2_hidden(X1,sK2)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f199,f43])).
% 1.77/0.63  fof(f199,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK3) | ~r2_orders_2(sK0,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK2)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f198,f42])).
% 1.77/0.63  fof(f198,plain,(
% 1.77/0.63    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK3) | ~r2_orders_2(sK0,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK2)) )),
% 1.77/0.63    inference(resolution,[],[f186,f45])).
% 1.77/0.63  fof(f186,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X0,sK0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X1) | ~r2_orders_2(sK0,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,X0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f185,f59])).
% 1.77/0.63  fof(f185,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X0,sK0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X1) | ~r2_orders_2(sK0,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,X0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f184,f59])).
% 1.77/0.63  fof(f184,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X0,sK0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X1) | ~r2_orders_2(sK0,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,X0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f183,f36])).
% 1.77/0.63  fof(f183,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X0,sK0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X1) | ~r2_orders_2(sK0,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,X0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f182,f37])).
% 1.77/0.63  fof(f182,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X0,sK0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X1) | ~r2_orders_2(sK0,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f181,f38])).
% 1.77/0.63  fof(f181,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X0,sK0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X1) | ~r2_orders_2(sK0,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(subsumption_resolution,[],[f180,f39])).
% 1.77/0.63  fof(f180,plain,(
% 1.77/0.63    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X0,sK0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X1) | ~r2_orders_2(sK0,X3,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.77/0.63    inference(resolution,[],[f50,f40])).
% 1.77/0.63  fof(f50,plain,(
% 1.77/0.63    ( ! [X4,X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,X4) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.77/0.63    inference(cnf_transformation,[],[f15])).
% 1.77/0.63  fof(f15,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.77/0.63    inference(flattening,[],[f14])).
% 1.77/0.63  fof(f14,plain,(
% 1.77/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X1,X4) | (~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.77/0.63    inference(ennf_transformation,[],[f7])).
% 1.77/0.63  fof(f7,axiom,(
% 1.77/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 1.77/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).
% 1.77/0.63  fof(f451,plain,(
% 1.77/0.63    ( ! [X4,X5] : (~r2_hidden(sK4(k3_orders_2(sK0,sK3,X4),X5),sK2) | r2_hidden(sK4(k3_orders_2(sK0,sK3,X4),X5),k3_orders_2(sK0,sK2,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X4),X5)) )),
% 1.77/0.63    inference(resolution,[],[f256,f42])).
% 1.77/0.63  fof(f256,plain,(
% 1.77/0.63    ( ! [X10,X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(sK4(k3_orders_2(sK0,sK3,X9),X10),k3_orders_2(sK0,X8,X9)) | ~r2_hidden(sK4(k3_orders_2(sK0,sK3,X9),X10),X8) | r1_tarski(k3_orders_2(sK0,sK3,X9),X10)) )),
% 1.77/0.63    inference(resolution,[],[f133,f43])).
% 1.77/0.63  % SZS output end Proof for theBenchmark
% 1.77/0.63  % (10763)------------------------------
% 1.77/0.63  % (10763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.63  % (10763)Termination reason: Refutation
% 1.77/0.63  
% 1.77/0.63  % (10763)Memory used [KB]: 6908
% 1.77/0.63  % (10763)Time elapsed: 0.182 s
% 1.77/0.63  % (10763)------------------------------
% 1.77/0.63  % (10763)------------------------------
% 1.77/0.63  % (10755)Success in time 0.257 s
%------------------------------------------------------------------------------
