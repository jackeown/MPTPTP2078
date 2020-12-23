%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 481 expanded)
%              Number of leaves         :   10 ( 166 expanded)
%              Depth                    :   20
%              Number of atoms          :  358 (3396 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f26,f28,f73,f83,f80,f82,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f82,plain,(
    ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f26,f28,f79,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f26,f28,f78])).

fof(f78,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( ~ r2_lattice3(sK0,sK1,sK3)
        & r2_lattice3(sK0,sK2,sK3) )
      | ( ~ r1_lattice3(sK0,sK1,sK3)
        & r1_lattice3(sK0,sK2,sK3) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ( ( ~ r2_lattice3(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3) )
                  | ( ~ r1_lattice3(X0,X1,X3)
                    & r1_lattice3(X0,X2,X3) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(sK0,X1,X3)
                  & r2_lattice3(sK0,X2,X3) )
                | ( ~ r1_lattice3(sK0,X1,X3)
                  & r1_lattice3(sK0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ( ( ~ r2_lattice3(sK0,X1,X3)
                & r2_lattice3(sK0,X2,X3) )
              | ( ~ r1_lattice3(sK0,X1,X3)
                & r1_lattice3(sK0,X2,X3) ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & r1_tarski(X1,X2) )
   => ( ? [X3] :
          ( ( ( ~ r2_lattice3(sK0,sK1,X3)
              & r2_lattice3(sK0,sK2,X3) )
            | ( ~ r1_lattice3(sK0,sK1,X3)
              & r1_lattice3(sK0,sK2,X3) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ( ( ~ r2_lattice3(sK0,sK1,X3)
            & r2_lattice3(sK0,sK2,X3) )
          | ( ~ r1_lattice3(sK0,sK1,X3)
            & r1_lattice3(sK0,sK2,X3) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,sK1,sK3)
          & r2_lattice3(sK0,sK2,sK3) )
        | ( ~ r1_lattice3(sK0,sK1,sK3)
          & r1_lattice3(sK0,sK2,sK3) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r2_lattice3(X0,X2,X3)
                   => r2_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                   => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f72,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (11227)Refutation not found, incomplete strategy% (11227)------------------------------
% (11227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3)
      | ~ r1_lattice3(sK0,sK1,sK3) ) ),
    inference(resolution,[],[f60,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | ~ r1_lattice3(sK0,sK1,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | ~ r1_lattice3(sK0,sK1,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3)
      | r2_lattice3(sK0,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
      | ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | ~ r1_lattice3(sK0,sK1,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | ~ m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK1,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK3)
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK1,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f28,f79,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    r2_hidden(sK5(sK0,sK1,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f81,f48])).

fof(f81,plain,(
    r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f26,f28,f79,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    r1_lattice3(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f26,f28,f70])).

fof(f70,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(resolution,[],[f65,f31])).

fof(f31,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3)
      | r1_lattice3(sK0,sK2,sK3) ) ),
    inference(resolution,[],[f55,f48])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | r1_lattice3(sK0,sK2,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | r1_lattice3(sK0,sK2,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3)
      | r2_lattice3(sK0,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
      | ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | r1_lattice3(sK0,sK2,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
      | ~ m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f45,f36])).

fof(f45,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK3)
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f29,f33])).

% (11227)Termination reason: Refutation not found, incomplete strategy

% (11227)Memory used [KB]: 895
% (11227)Time elapsed: 0.007 s
% (11227)------------------------------
% (11227)------------------------------
fof(f29,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:57:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (11217)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (11225)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (11227)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (11217)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f28,f73,f83,f80,f82,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(rectify,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f28,f79,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f28,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK1,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.49    inference(resolution,[],[f72,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~r2_lattice3(sK0,sK1,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ((((~r2_lattice3(sK0,sK1,sK3) & r2_lattice3(sK0,sK2,sK3)) | (~r1_lattice3(sK0,sK1,sK3) & r1_lattice3(sK0,sK2,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0))) & r1_tarski(sK1,sK2)) & l1_orders_2(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0)) => (? [X2,X1] : (? [X3] : (((~r2_lattice3(sK0,X1,X3) & r2_lattice3(sK0,X2,X3)) | (~r1_lattice3(sK0,X1,X3) & r1_lattice3(sK0,X2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(X1,X2)) & l1_orders_2(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X2,X1] : (? [X3] : (((~r2_lattice3(sK0,X1,X3) & r2_lattice3(sK0,X2,X3)) | (~r1_lattice3(sK0,X1,X3) & r1_lattice3(sK0,X2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(X1,X2)) => (? [X3] : (((~r2_lattice3(sK0,sK1,X3) & r2_lattice3(sK0,sK2,X3)) | (~r1_lattice3(sK0,sK1,X3) & r1_lattice3(sK0,sK2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(sK1,sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X3] : (((~r2_lattice3(sK0,sK1,X3) & r2_lattice3(sK0,sK2,X3)) | (~r1_lattice3(sK0,sK1,X3) & r1_lattice3(sK0,sK2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) => (((~r2_lattice3(sK0,sK1,sK3) & r2_lattice3(sK0,sK2,sK3)) | (~r1_lattice3(sK0,sK1,sK3) & r1_lattice3(sK0,sK2,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    r2_lattice3(sK0,sK1,sK3) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,sK1,sK3) | ~r1_lattice3(sK0,sK1,sK3) | r2_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(resolution,[],[f61,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  % (11227)Refutation not found, incomplete strategy% (11227)------------------------------
% 0.21/0.49  % (11227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(rectify,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3) | ~r1_lattice3(sK0,sK1,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f60,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f44,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f27,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK2) | ~r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK2) | ~r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3) | r2_lattice3(sK0,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f53,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,X0,sK3),sK2) | ~r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK2) | ~m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f49,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK4(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(sK0,X0,sK3) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f30,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f28,f79,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    r2_hidden(sK5(sK0,sK1,sK3),sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f81,f48])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f28,f79,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f28,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f65,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~r2_lattice3(sK0,sK1,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    r2_lattice3(sK0,sK1,sK3) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,sK1,sK3) | r1_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(resolution,[],[f56,f35])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3) | r1_lattice3(sK0,sK2,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f55,f48])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK2) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK2) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3) | r2_lattice3(sK0,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f51,f34])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,X0,sK3),sK2) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,sK3),sK2) | ~m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f45,f36])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(sK0,X0,sK3) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f29,f33])).
% 0.21/0.49  % (11227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11227)Memory used [KB]: 895
% 0.21/0.49  % (11227)Time elapsed: 0.007 s
% 0.21/0.49  % (11227)------------------------------
% 0.21/0.49  % (11227)------------------------------
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11217)------------------------------
% 0.21/0.49  % (11217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11217)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11217)Memory used [KB]: 895
% 0.21/0.49  % (11217)Time elapsed: 0.065 s
% 0.21/0.49  % (11217)------------------------------
% 0.21/0.49  % (11217)------------------------------
% 0.21/0.49  % (11211)Success in time 0.127 s
%------------------------------------------------------------------------------
