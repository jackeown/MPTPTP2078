%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 606 expanded)
%              Number of leaves         :   12 ( 203 expanded)
%              Depth                    :   37
%              Number of atoms          :  612 (3231 expanded)
%              Number of equality atoms :  122 (1109 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(subsumption_resolution,[],[f202,f32])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    & r2_yellow_0(sK0,sK2)
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                & r2_yellow_0(X0,X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X1,X2) != k2_yellow_0(sK0,X2)
              & r2_yellow_0(sK0,X2) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_yellow_0(X1,X2) != k2_yellow_0(sK0,X2)
            & r2_yellow_0(sK0,X2) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( k2_yellow_0(sK0,X2) != k2_yellow_0(sK1,X2)
          & r2_yellow_0(sK0,X2) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( k2_yellow_0(sK0,X2) != k2_yellow_0(sK1,X2)
        & r2_yellow_0(sK0,X2) )
   => ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
      & r2_yellow_0(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( r2_yellow_0(X0,X2)
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_0)).

fof(f202,plain,(
    ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f201,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f201,plain,(
    ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f200,f32])).

fof(f200,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f199,f35])).

fof(f35,plain,(
    r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f199,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f198,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f59,f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f198,plain,
    ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f196,f142])).

fof(f142,plain,(
    ! [X2,X3] :
      ( r1_lattice3(sK1,X3,X2)
      | ~ r1_lattice3(sK0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,X3,X2)
      | r1_lattice3(sK1,X3,X2) ) ),
    inference(forward_demodulation,[],[f140,f65])).

fof(f65,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f61,f34])).

fof(f34,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f60,f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f140,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,X3,X2)
      | r1_lattice3(sK1,X3,X2) ) ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      | ~ r1_lattice3(sK0,X3,X2)
      | r1_lattice3(sK1,X3,X2) ) ),
    inference(resolution,[],[f133,f33])).

fof(f33,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ r1_lattice3(sK0,X0,X1)
      | r1_lattice3(X2,X0,X1) ) ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | r1_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f196,plain,
    ( ~ r1_lattice3(sK1,sK2,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f195,f126])).

fof(f126,plain,(
    r2_yellow_0(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | r2_yellow_0(sK1,sK2) ),
    inference(resolution,[],[f123,f32])).

fof(f123,plain,(
    ! [X1] :
      ( ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | r2_yellow_0(sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X1] :
      ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X1)
      | r2_yellow_0(sK1,sK2)
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ) ),
    inference(forward_demodulation,[],[f120,f34])).

fof(f120,plain,(
    ! [X1] :
      ( ~ l1_orders_2(X1)
      | r2_yellow_0(sK1,sK2)
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f111,f33])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X1,sK2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X1,sK2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f109,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | r2_yellow_0(X1,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( r2_yellow_0(X0,X2)
                 => r2_yellow_0(X1,X2) )
                & ( r1_yellow_0(X0,X2)
                 => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_0)).

fof(f109,plain,(
    ! [X0] :
      ( r2_yellow_0(X0,sK2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f108,f32])).

fof(f108,plain,(
    ! [X0] :
      ( r2_yellow_0(X0,sK2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f39,f35])).

fof(f195,plain,
    ( ~ r1_lattice3(sK1,sK2,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f194,f36])).

fof(f36,plain,(
    k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f194,plain,
    ( k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ r1_lattice3(sK1,sK2,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ r1_lattice3(sK1,sK2,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ r1_lattice3(sK1,sK2,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(resolution,[],[f192,f158])).

fof(f158,plain,(
    ! [X4,X3] :
      ( r1_lattice3(sK0,X3,sK3(sK1,X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_yellow_0(sK1,X3) = X4
      | ~ r1_lattice3(sK1,X3,X4)
      | ~ r2_yellow_0(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f157,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(sK1,X0,X1),u1_struct_0(sK0))
      | k2_yellow_0(sK1,X0) = X1
      | ~ r1_lattice3(sK1,X0,X1)
      | ~ r2_yellow_0(sK1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f112,f33])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(sK1,X0,X1),u1_struct_0(sK0))
      | k2_yellow_0(sK1,X0) = X1
      | ~ r1_lattice3(sK1,X0,X1)
      | ~ r2_yellow_0(sK1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f46,f65])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f157,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(sK1,X3,X4),u1_struct_0(sK0))
      | r1_lattice3(sK0,X3,sK3(sK1,X3,X4))
      | k2_yellow_0(sK1,X3) = X4
      | ~ r1_lattice3(sK1,X3,X4)
      | ~ r2_yellow_0(sK1,X3) ) ),
    inference(forward_demodulation,[],[f156,f65])).

fof(f156,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK1,X3,X4),u1_struct_0(sK0))
      | r1_lattice3(sK0,X3,sK3(sK1,X3,X4))
      | k2_yellow_0(sK1,X3) = X4
      | ~ r1_lattice3(sK1,X3,X4)
      | ~ r2_yellow_0(sK1,X3)
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f152,f33])).

fof(f152,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK1,X3,X4),u1_struct_0(sK0))
      | r1_lattice3(sK0,X3,sK3(sK1,X3,X4))
      | k2_yellow_0(sK1,X3) = X4
      | ~ r1_lattice3(sK1,X3,X4)
      | ~ r2_yellow_0(sK1,X3)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f149,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK1,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK1,X1,X0)
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | r1_lattice3(sK0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK1,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | r1_lattice3(sK0,X1,X0) ) ),
    inference(resolution,[],[f136,f32])).

fof(f136,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_orders_2(X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_lattice3(sK1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | r1_lattice3(X5,X3,X4) ) ),
    inference(forward_demodulation,[],[f135,f34])).

fof(f135,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_lattice3(sK1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | r1_lattice3(X5,X3,X4) ) ),
    inference(forward_demodulation,[],[f134,f65])).

fof(f134,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_lattice3(sK1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | r1_lattice3(X5,X3,X4) ) ),
    inference(resolution,[],[f56,f33])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,sK3(sK1,X0,k2_yellow_0(sK0,sK2)))
      | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,X0)
      | ~ r1_lattice3(sK1,X0,k2_yellow_0(sK0,sK2))
      | ~ r2_yellow_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f191,f32])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,sK3(sK1,X0,k2_yellow_0(sK0,sK2)))
      | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,X0)
      | ~ r1_lattice3(sK1,X0,k2_yellow_0(sK0,sK2))
      | ~ r2_yellow_0(sK1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f185,f49])).

fof(f185,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,sK3(sK1,X0,k2_yellow_0(sK0,sK2)))
      | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,X0)
      | ~ r1_lattice3(sK1,X0,k2_yellow_0(sK0,sK2))
      | ~ r2_yellow_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f184,f113])).

fof(f184,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,sK3(sK1,X0,k2_yellow_0(sK0,sK2)))
      | ~ m1_subset_1(sK3(sK1,X0,k2_yellow_0(sK0,sK2)),u1_struct_0(sK0))
      | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,X0)
      | ~ r1_lattice3(sK1,X0,k2_yellow_0(sK0,sK2))
      | ~ r2_yellow_0(sK1,X0) ) ),
    inference(forward_demodulation,[],[f183,f65])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,sK3(sK1,X0,k2_yellow_0(sK0,sK2)))
      | ~ m1_subset_1(sK3(sK1,X0,k2_yellow_0(sK0,sK2)),u1_struct_0(sK0))
      | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,X0)
      | ~ r1_lattice3(sK1,X0,k2_yellow_0(sK0,sK2))
      | ~ r2_yellow_0(sK1,X0)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f181,f33])).

fof(f181,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,sK3(sK1,X0,k2_yellow_0(sK0,sK2)))
      | ~ m1_subset_1(sK3(sK1,X0,k2_yellow_0(sK0,sK2)),u1_struct_0(sK0))
      | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,X0)
      | ~ r1_lattice3(sK1,X0,k2_yellow_0(sK0,sK2))
      | ~ r2_yellow_0(sK1,X0)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f177,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f177,plain,(
    ! [X0] :
      ( r1_orders_2(sK1,X0,k2_yellow_0(sK0,sK2))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f176,f35])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,X1)
      | r1_orders_2(sK1,X0,k2_yellow_0(sK0,X1))
      | ~ r1_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f175,f32])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,k2_yellow_0(sK0,X1))
      | ~ r1_lattice3(sK0,X1,X0)
      | ~ r2_yellow_0(sK0,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f174,f49])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK1,X1,k2_yellow_0(sK0,X0))
      | ~ r1_lattice3(sK0,X0,X1)
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f173,f33])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1)
      | r1_orders_2(sK1,X1,k2_yellow_0(sK0,X0))
      | ~ r1_lattice3(sK0,X0,X1)
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f66,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(superposition,[],[f34,f65])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(sK1)
      | r1_orders_2(sK1,X1,k2_yellow_0(sK0,X0))
      | ~ r1_lattice3(sK0,X0,X1)
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(sK1)
      | r1_orders_2(sK1,X1,k2_yellow_0(sK0,X0))
      | ~ r1_lattice3(sK0,X0,X1)
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(superposition,[],[f164,f65])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X2,k2_yellow_0(sK0,X0))
      | ~ r1_lattice3(sK0,X0,X2)
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f163,f32])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X2)
      | ~ m1_subset_1(k2_yellow_0(X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,k2_yellow_0(X2,X3))
      | ~ r1_lattice3(X2,X3,X1)
      | ~ r2_yellow_0(X2,X3) ) ),
    inference(subsumption_resolution,[],[f162,f49])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k2_yellow_0(X2,X3))
      | ~ m1_subset_1(k2_yellow_0(X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k2_yellow_0(X2,X3),u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X2)
      | ~ r1_lattice3(X2,X3,X1)
      | ~ r2_yellow_0(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k2_yellow_0(X2,X3))
      | ~ m1_subset_1(k2_yellow_0(X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k2_yellow_0(X2,X3),u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X2)
      | ~ r1_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ r2_yellow_0(X2,X3)
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f55,f114])).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f58,f49])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

%------------------------------------------------------------------------------
