%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1548+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:04 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  125 (1073 expanded)
%              Number of leaves         :   14 ( 364 expanded)
%              Depth                    :   31
%              Number of atoms          :  574 (5017 expanded)
%              Number of equality atoms :   95 (1830 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(global_subsumption,[],[f41,f466])).

fof(f466,plain,(
    k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,sK4) ),
    inference(resolution,[],[f465,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ sP0(k1_yellow_0(sK3,X0),sK2,sK4)
      | k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,X0) ) ),
    inference(resolution,[],[f105,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k1_yellow_0(X1,X0) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_yellow_0(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_yellow_0(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_yellow_0(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_yellow_0(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( k1_yellow_0(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f105,plain,(
    ! [X0] : sP1(sK4,sK2,k1_yellow_0(sK3,X0)) ),
    inference(resolution,[],[f103,f40])).

fof(f40,plain,(
    r1_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
    & r1_yellow_0(sK2,sK4)
    & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & l1_orders_2(sK3)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                & r1_yellow_0(X0,X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X1,X2) != k1_yellow_0(sK2,X2)
              & r1_yellow_0(sK2,X2) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
          & l1_orders_2(X1) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_yellow_0(X1,X2) != k1_yellow_0(sK2,X2)
            & r1_yellow_0(sK2,X2) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( k1_yellow_0(sK2,X2) != k1_yellow_0(sK3,X2)
          & r1_yellow_0(sK2,X2) )
      & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( k1_yellow_0(sK2,X2) != k1_yellow_0(sK3,X2)
        & r1_yellow_0(sK2,X2) )
   => ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
      & r1_yellow_0(sK2,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
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
                  ( r1_yellow_0(X0,X2)
                 => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_0)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK2,X0)
      | sP1(X0,sK2,k1_yellow_0(sK3,X1)) ) ),
    inference(resolution,[],[f102,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_yellow_0(sK2,X0)
      | sP1(X0,sK2,X1) ) ),
    inference(resolution,[],[f56,f37])).

fof(f37,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X1,X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f20,f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f102,plain,(
    ! [X5] : m1_subset_1(k1_yellow_0(sK3,X5),u1_struct_0(sK2)) ),
    inference(global_subsumption,[],[f38,f99])).

fof(f99,plain,(
    ! [X5] :
      ( m1_subset_1(k1_yellow_0(sK3,X5),u1_struct_0(sK2))
      | ~ l1_orders_2(sK3) ) ),
    inference(superposition,[],[f57,f90])).

fof(f90,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(global_subsumption,[],[f37,f89])).

fof(f89,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f88,f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f88,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_struct_0(sK3) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f58,f39])).

fof(f39,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f38,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f465,plain,(
    sP0(k1_yellow_0(sK3,sK4),sK2,sK4) ),
    inference(global_subsumption,[],[f284,f464])).

fof(f464,plain,
    ( ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4))
    | sP0(k1_yellow_0(sK3,sK4),sK2,sK4) ),
    inference(resolution,[],[f463,f167])).

fof(f167,plain,(
    sP0(k1_yellow_0(sK3,sK4),sK3,sK4) ),
    inference(resolution,[],[f166,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1,k1_yellow_0(X1,X0))
      | sP0(k1_yellow_0(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_yellow_0(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f166,plain,(
    ! [X0] : sP1(sK4,sK3,k1_yellow_0(sK3,X0)) ),
    inference(resolution,[],[f163,f40])).

fof(f163,plain,(
    ! [X10,X9] :
      ( ~ r1_yellow_0(sK2,X9)
      | sP1(X9,sK3,k1_yellow_0(sK3,X10)) ) ),
    inference(resolution,[],[f158,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK3,X0)
      | sP1(X0,sK3,k1_yellow_0(sK3,X1)) ) ),
    inference(global_subsumption,[],[f38,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK3,X0)
      | sP1(X0,sK3,k1_yellow_0(sK3,X1))
      | ~ l1_orders_2(sK3) ) ),
    inference(resolution,[],[f68,f57])).

fof(f68,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ r1_yellow_0(sK3,X2)
      | sP1(X2,sK3,X3) ) ),
    inference(resolution,[],[f56,f38])).

fof(f158,plain,(
    ! [X0] :
      ( r1_yellow_0(sK3,X0)
      | ~ r1_yellow_0(sK2,X0) ) ),
    inference(global_subsumption,[],[f37,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK3,X0)
      | ~ l1_orders_2(sK2) ) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(sK3,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(global_subsumption,[],[f38,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(sK3,X1)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X0) ) ),
    inference(forward_demodulation,[],[f141,f130])).

fof(f130,plain,(
    u1_orders_2(sK2) = u1_orders_2(sK3) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_orders_2(sK3) = X1 ) ),
    inference(global_subsumption,[],[f100,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_orders_2(sK3) = X1
      | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ) ),
    inference(superposition,[],[f59,f94])).

fof(f94,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3)) ),
    inference(backward_demodulation,[],[f39,f90])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,(
    m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f38,f98])).

fof(f98,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK3) ),
    inference(superposition,[],[f42,f90])).

fof(f141,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(sK3,X1)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f43,f90])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_yellow_0(X0,X2)
      | r1_yellow_0(X1,X2)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_0)).

fof(f463,plain,(
    ! [X0,X1] :
      ( ~ sP0(k1_yellow_0(sK3,X0),sK3,X1)
      | ~ r2_lattice3(sK2,X1,k1_yellow_0(sK3,X0))
      | sP0(k1_yellow_0(sK3,X0),sK2,X1) ) ),
    inference(duplicate_literal_removal,[],[f462])).

fof(f462,plain,(
    ! [X0,X1] :
      ( sP0(k1_yellow_0(sK3,X0),sK2,X1)
      | ~ r2_lattice3(sK2,X1,k1_yellow_0(sK3,X0))
      | ~ sP0(k1_yellow_0(sK3,X0),sK3,X1)
      | sP0(k1_yellow_0(sK3,X0),sK2,X1)
      | ~ r2_lattice3(sK2,X1,k1_yellow_0(sK3,X0)) ) ),
    inference(resolution,[],[f461,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
          & r2_lattice3(X1,X2,sK5(X0,X1,X2))
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r2_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X0,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
        & r2_lattice3(X1,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ r2_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X0,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X2) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X2) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f461,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK2,k1_yellow_0(sK3,X0),sK5(X1,sK2,X2))
      | sP0(X1,sK2,X2)
      | ~ r2_lattice3(sK2,X2,X1)
      | ~ sP0(k1_yellow_0(sK3,X0),sK3,X2) ) ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK2,k1_yellow_0(sK3,X0),sK5(X1,sK2,X2))
      | sP0(X1,sK2,X2)
      | ~ r2_lattice3(sK2,X2,X1)
      | ~ r2_lattice3(sK2,X2,X1)
      | sP0(X1,sK2,X2)
      | ~ sP0(k1_yellow_0(sK3,X0),sK3,X2) ) ),
    inference(resolution,[],[f447,f316])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK3,X2,sK5(X0,sK2,X1))
      | ~ r2_lattice3(sK2,X1,X0)
      | sP0(X0,sK2,X1)
      | ~ sP0(X2,sK3,X1) ) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,sK2,X1)
      | ~ r2_lattice3(sK2,X1,X0)
      | r1_orders_2(sK3,X2,sK5(X0,sK2,X1))
      | ~ sP0(X2,sK3,X1)
      | sP0(X0,sK2,X1)
      | ~ r2_lattice3(sK2,X1,X0) ) ),
    inference(resolution,[],[f309,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f309,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_lattice3(sK2,X3,sK5(X4,sK2,X5))
      | sP0(X4,sK2,X5)
      | ~ r2_lattice3(sK2,X5,X4)
      | r1_orders_2(sK3,X6,sK5(X4,sK2,X5))
      | ~ sP0(X6,sK3,X3) ) ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_lattice3(sK2,X3,sK5(X4,sK2,X5))
      | sP0(X4,sK2,X5)
      | ~ r2_lattice3(sK2,X5,X4)
      | r1_orders_2(sK3,X6,sK5(X4,sK2,X5))
      | ~ sP0(X6,sK3,X3)
      | sP0(X4,sK2,X5)
      | ~ r2_lattice3(sK2,X5,X4) ) ),
    inference(resolution,[],[f298,f120])).

fof(f120,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_lattice3(sK3,X6,sK5(X7,sK2,X8))
      | r1_orders_2(sK3,X9,sK5(X7,sK2,X8))
      | ~ sP0(X9,sK3,X6)
      | sP0(X7,sK2,X8)
      | ~ r2_lattice3(sK2,X8,X7) ) ),
    inference(resolution,[],[f96,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_lattice3(sK3,X1,X0)
      | r1_orders_2(sK3,X2,X0)
      | ~ sP0(X2,sK3,X1) ) ),
    inference(superposition,[],[f52,f90])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_lattice3(X1,X2,X4)
      | r1_orders_2(X1,X0,X4)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f298,plain,(
    ! [X6,X4,X5] :
      ( r2_lattice3(sK3,X4,sK5(X5,sK2,X6))
      | ~ r2_lattice3(sK2,X4,sK5(X5,sK2,X6))
      | sP0(X5,sK2,X6)
      | ~ r2_lattice3(sK2,X6,X5) ) ),
    inference(resolution,[],[f295,f53])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X1)
      | r2_lattice3(sK3,X0,X1) ) ),
    inference(global_subsumption,[],[f37,f293])).

fof(f293,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK3,X0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK3,X0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(equality_resolution,[],[f254])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(sK3,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(global_subsumption,[],[f38,f253])).

% (29762)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f253,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(sK3,X1,X2)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X0) ) ),
    inference(forward_demodulation,[],[f245,f130])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(sK3,X1,X2)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f65,f90])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X1,X2,X4)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f447,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(sK3,k1_yellow_0(sK3,X3),sK5(X4,sK2,X5))
      | r1_orders_2(sK2,k1_yellow_0(sK3,X3),sK5(X4,sK2,X5))
      | sP0(X4,sK2,X5)
      | ~ r2_lattice3(sK2,X5,X4) ) ),
    inference(resolution,[],[f429,f102])).

fof(f429,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X4,sK5(X5,sK2,X6))
      | r1_orders_2(sK2,X4,sK5(X5,sK2,X6))
      | sP0(X5,sK2,X6)
      | ~ r2_lattice3(sK2,X6,X5) ) ),
    inference(resolution,[],[f426,f53])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1) ) ),
    inference(global_subsumption,[],[f37,f424])).

fof(f424,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(duplicate_literal_removal,[],[f423])).

% (29745)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f423,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(equality_resolution,[],[f357])).

fof(f357,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r1_orders_2(sK3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(global_subsumption,[],[f38,f356])).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r1_orders_2(sK3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK3) ) ),
    inference(forward_demodulation,[],[f350,f130])).

fof(f350,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ r1_orders_2(sK3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK3) ) ),
    inference(superposition,[],[f63,f90])).

fof(f63,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
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
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f284,plain,(
    r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4)) ),
    inference(resolution,[],[f280,f169])).

fof(f169,plain,(
    r2_lattice3(sK3,sK4,k1_yellow_0(sK3,sK4)) ),
    inference(resolution,[],[f167,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f280,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK3,X2,k1_yellow_0(sK3,X3))
      | r2_lattice3(sK2,X2,k1_yellow_0(sK3,X3)) ) ),
    inference(resolution,[],[f278,f102])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK3,X0,X1)
      | r2_lattice3(sK2,X0,X1) ) ),
    inference(global_subsumption,[],[f37,f276])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,X0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,X0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(equality_resolution,[],[f250])).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r2_lattice3(sK3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(global_subsumption,[],[f38,f249])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r2_lattice3(sK3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK3) ) ),
    inference(forward_demodulation,[],[f243,f130])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ r2_lattice3(sK3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK3) ) ),
    inference(superposition,[],[f65,f90])).

fof(f41,plain,(
    k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
