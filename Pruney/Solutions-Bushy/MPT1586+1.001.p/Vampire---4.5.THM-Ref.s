%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1586+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:09 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  221 (29057 expanded)
%              Number of leaves         :   25 (10379 expanded)
%              Depth                    :   52
%              Number of atoms          : 1179 (274765 expanded)
%              Number of equality atoms :   86 (25661 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1324,f1302])).

fof(f1302,plain,(
    k1_yellow_0(sK5,sK7) != k1_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f79,f1300])).

fof(f1300,plain,(
    r1_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f1299,f132])).

fof(f132,plain,(
    l1_orders_2(sK6) ),
    inference(resolution,[],[f131,f75])).

fof(f75,plain,(
    m1_yellow_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( k1_yellow_0(sK5,sK7) != k1_yellow_0(sK6,sK7)
      | ~ r1_yellow_0(sK6,sK7) )
    & r2_hidden(k1_yellow_0(sK5,sK7),u1_struct_0(sK6))
    & r1_yellow_0(sK5,sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_yellow_0(sK6,sK5)
    & v4_yellow_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_orders_2(sK5)
    & v4_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                  | ~ r1_yellow_0(X1,X2) )
                & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                & r1_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X1,X2) != k1_yellow_0(sK5,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(sK5,X2),u1_struct_0(X1))
              & r1_yellow_0(sK5,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK5)
          & v4_yellow_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK5)
      & v4_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k1_yellow_0(X1,X2) != k1_yellow_0(sK5,X2)
              | ~ r1_yellow_0(X1,X2) )
            & r2_hidden(k1_yellow_0(sK5,X2),u1_struct_0(X1))
            & r1_yellow_0(sK5,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_yellow_0(X1,sK5)
        & v4_yellow_0(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k1_yellow_0(sK5,X2) != k1_yellow_0(sK6,X2)
            | ~ r1_yellow_0(sK6,X2) )
          & r2_hidden(k1_yellow_0(sK5,X2),u1_struct_0(sK6))
          & r1_yellow_0(sK5,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
      & m1_yellow_0(sK6,sK5)
      & v4_yellow_0(sK6,sK5)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ( k1_yellow_0(sK5,X2) != k1_yellow_0(sK6,X2)
          | ~ r1_yellow_0(sK6,X2) )
        & r2_hidden(k1_yellow_0(sK5,X2),u1_struct_0(sK6))
        & r1_yellow_0(sK5,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ( k1_yellow_0(sK5,sK7) != k1_yellow_0(sK6,sK7)
        | ~ r1_yellow_0(sK6,sK7) )
      & r2_hidden(k1_yellow_0(sK5,sK7),u1_struct_0(sK6))
      & r1_yellow_0(sK5,sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                    & r1_yellow_0(X0,X2) )
                 => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                    & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_yellow_0)).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_yellow_0(X0,sK5)
      | l1_orders_2(X0) ) ),
    inference(resolution,[],[f80,f72])).

fof(f72,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f1299,plain,
    ( r1_yellow_0(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f1289,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f84,f99])).

fof(f99,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f25,f43,f42,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              & r2_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f42,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ? [X2] :
          ( sP0(X2,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X2,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> sP1(X1,X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0)
      | ~ sP1(X1,X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ~ sP1(X1,X0) )
          & ( sP1(X1,X0)
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f1289,plain,(
    sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f1288,f1281])).

fof(f1281,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f1154,f1280])).

fof(f1280,plain,(
    sP0(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(trivial_inequality_removal,[],[f1274])).

fof(f1274,plain,
    ( k1_yellow_0(sK5,sK7) != k1_yellow_0(sK5,sK7)
    | sP0(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(superposition,[],[f98,f1205])).

fof(f1205,plain,(
    k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f1204,f1172])).

fof(f1172,plain,
    ( k1_yellow_0(sK5,sK7) != k1_yellow_0(sK6,sK7)
    | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f1169,f79])).

fof(f1169,plain,
    ( r1_yellow_0(sK6,sK7)
    | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f1168,f132])).

fof(f1168,plain,
    ( k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7)
    | r1_yellow_0(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f1159,f134])).

fof(f1159,plain,
    ( sP1(sK7,sK6)
    | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f1156,f582])).

fof(f582,plain,
    ( m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f576,f455])).

fof(f455,plain,(
    r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f453,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
          & r2_lattice3(X1,X2,sK12(X0,X1,X2))
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r2_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X0,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X0) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
        & r2_lattice3(X1,X2,sK12(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
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
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
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
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
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
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f453,plain,(
    sP3(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f452,f145])).

fof(f145,plain,(
    r2_lattice3(sK5,sK7,k1_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f143,f102])).

fof(f143,plain,(
    sP3(k1_yellow_0(sK5,sK7),sK5,sK7) ),
    inference(resolution,[],[f142,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1,k1_yellow_0(X1,X0))
      | sP3(k1_yellow_0(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k1_yellow_0(X1,X0) != X2
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_yellow_0(X1,X0) = X2
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | k1_yellow_0(X1,X0) != X2 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_yellow_0(X0,X1) = X2
          | ~ sP3(X2,X0,X1) )
        & ( sP3(X2,X0,X1)
          | k1_yellow_0(X0,X1) != X2 ) )
      | ~ sP4(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( k1_yellow_0(X0,X1) = X2
      <=> sP3(X2,X0,X1) )
      | ~ sP4(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f142,plain,(
    ! [X0] : sP4(sK7,sK5,k1_yellow_0(sK5,X0)) ),
    inference(subsumption_resolution,[],[f139,f72])).

fof(f139,plain,(
    ! [X0] :
      ( sP4(sK7,sK5,k1_yellow_0(sK5,X0))
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f138,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
      | sP4(sK7,sK5,X0) ) ),
    inference(subsumption_resolution,[],[f137,f72])).

fof(f137,plain,(
    ! [X0] :
      ( sP4(sK7,sK5,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f107,f77])).

fof(f77,plain,(
    r1_yellow_0(sK5,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | sP4(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X1,X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f27,f46,f45])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f452,plain,
    ( sP3(k1_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r2_lattice3(sK5,sK7,k1_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f451,f280])).

fof(f280,plain,(
    ! [X0] :
      ( r2_lattice3(sK6,X0,k1_yellow_0(sK5,sK7))
      | ~ r2_lattice3(sK5,X0,k1_yellow_0(sK5,sK7)) ) ),
    inference(resolution,[],[f279,f130])).

fof(f130,plain,(
    m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f115,f78])).

fof(f78,plain,(
    r2_hidden(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ r2_lattice3(sK5,X0,X1)
      | r2_lattice3(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f278,f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f157,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f156,f72])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f155,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f110,f75])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_yellow_0)).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r2_lattice3(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f277,f70])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r2_lattice3(sK6,X0,X1)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f276,f72])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r2_lattice3(sK6,X0,X1)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f275,f73])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r2_lattice3(sK6,X0,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f274,f75])).

fof(f274,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_yellow_0(sK6,sK5)
      | r2_lattice3(sK6,X0,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f123,f74])).

fof(f74,plain,(
    v4_yellow_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | r2_lattice3(X1,X2,X4)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X3 = X4
                   => ( ( r2_lattice3(X0,X2,X3)
                       => r2_lattice3(X1,X2,X4) )
                      & ( r1_lattice3(X0,X2,X3)
                       => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_yellow_0)).

fof(f451,plain,
    ( ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7))
    | sP3(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(duplicate_literal_removal,[],[f450])).

fof(f450,plain,
    ( sP3(k1_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7))
    | sP3(k1_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f414,f251])).

fof(f251,plain,(
    ! [X3] :
      ( r2_lattice3(sK5,sK7,sK12(X3,sK6,sK7))
      | sP3(X3,sK6,sK7)
      | ~ r2_lattice3(sK6,sK7,X3) ) ),
    inference(subsumption_resolution,[],[f246,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f246,plain,(
    ! [X3] :
      ( r2_lattice3(sK5,sK7,sK12(X3,sK6,sK7))
      | ~ m1_subset_1(sK12(X3,sK6,sK7),u1_struct_0(sK6))
      | sP3(X3,sK6,sK7)
      | ~ r2_lattice3(sK6,sK7,X3) ) ),
    inference(resolution,[],[f241,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK12(X0,X1,X2))
      | sP3(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK6,sK7,X0)
      | r2_lattice3(sK5,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f240,f70])).

fof(f240,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_lattice3(sK5,sK7,X0)
      | ~ r2_lattice3(sK6,sK7,X0)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f239,f72])).

fof(f239,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_lattice3(sK5,sK7,X0)
      | ~ r2_lattice3(sK6,sK7,X0)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f238,f75])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(sK6,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_lattice3(X1,sK7,X0)
      | ~ r2_lattice3(sK6,sK7,X0)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f237,f73])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK6,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_lattice3(X1,sK7,X0)
      | ~ m1_yellow_0(sK6,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f127,f76])).

fof(f76,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f51])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_lattice3(X0,X2,X4)
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f125,f110])).

fof(f125,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X0,X2,X4)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X1,X2,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_yellow_0)).

fof(f414,plain,(
    ! [X1] :
      ( ~ r2_lattice3(sK5,sK7,sK12(k1_yellow_0(sK5,sK7),sK6,X1))
      | sP3(k1_yellow_0(sK5,sK7),sK6,X1)
      | ~ r2_lattice3(sK6,X1,k1_yellow_0(sK5,sK7)) ) ),
    inference(subsumption_resolution,[],[f409,f104])).

fof(f409,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK12(k1_yellow_0(sK5,sK7),sK6,X1),u1_struct_0(sK6))
      | ~ r2_lattice3(sK5,sK7,sK12(k1_yellow_0(sK5,sK7),sK6,X1))
      | sP3(k1_yellow_0(sK5,sK7),sK6,X1)
      | ~ r2_lattice3(sK6,X1,k1_yellow_0(sK5,sK7)) ) ),
    inference(resolution,[],[f401,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
      | sP3(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f401,plain,(
    ! [X0] :
      ( r1_orders_2(sK6,k1_yellow_0(sK5,sK7),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ r2_lattice3(sK5,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f399,f158])).

fof(f399,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_orders_2(sK6,k1_yellow_0(sK5,sK7),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ r2_lattice3(sK5,sK7,X0) ) ),
    inference(resolution,[],[f397,f150])).

fof(f150,plain,(
    ! [X0] :
      ( r1_orders_2(sK5,k1_yellow_0(sK5,sK7),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ r2_lattice3(sK5,sK7,X0) ) ),
    inference(resolution,[],[f103,f143])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f397,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK5,k1_yellow_0(sK5,sK7),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_orders_2(sK6,k1_yellow_0(sK5,sK7),X0) ) ),
    inference(subsumption_resolution,[],[f395,f159])).

fof(f159,plain,(
    m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK5)) ),
    inference(resolution,[],[f158,f130])).

fof(f395,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK5,k1_yellow_0(sK5,sK7),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK5))
      | r1_orders_2(sK6,k1_yellow_0(sK5,sK7),X0) ) ),
    inference(resolution,[],[f394,f78])).

fof(f394,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f393,f158])).

fof(f393,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f392,f72])).

fof(f392,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(subsumption_resolution,[],[f391,f75])).

fof(f391,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_yellow_0(sK6,sK5)
      | r1_orders_2(sK6,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f129,f74])).

fof(f129,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f121,f115])).

fof(f121,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

fof(f576,plain,
    ( sP1(sK7,sK6)
    | m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7))
    | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f557,f130])).

fof(f557,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK6))
      | sP1(sK7,sK6)
      | m1_subset_1(sK8(sK7,sK6,X4),u1_struct_0(sK6))
      | ~ r2_lattice3(sK6,sK7,X4)
      | k1_yellow_0(sK5,sK7) = sK10(X4,sK6,sK7) ) ),
    inference(resolution,[],[f548,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ sP0(X2,X1,X0)
            | ( ~ r1_orders_2(X1,X2,sK8(X0,X1,X2))
              & r2_lattice3(X1,X0,sK8(X0,X1,X2))
              & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ( sP0(sK9(X0,X1),X1,X0)
          & ! [X5] :
              ( r1_orders_2(X1,sK9(X0,X1),X5)
              | ~ r2_lattice3(X1,X0,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r2_lattice3(X1,X0,sK9(X0,X1))
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f54,f56,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X2,X3)
          & r2_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X2,sK8(X0,X1,X2))
        & r2_lattice3(X1,X0,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X1,X0)
          & ! [X5] :
              ( r1_orders_2(X1,X4,X5)
              | ~ r2_lattice3(X1,X0,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r2_lattice3(X1,X0,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP0(sK9(X0,X1),X1,X0)
        & ! [X5] :
            ( r1_orders_2(X1,sK9(X0,X1),X5)
            | ~ r2_lattice3(X1,X0,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & r2_lattice3(X1,X0,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ sP0(X2,X1,X0)
            | ? [X3] :
                ( ~ r1_orders_2(X1,X2,X3)
                & r2_lattice3(X1,X0,X3)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP0(X4,X1,X0)
            & ! [X5] :
                ( r1_orders_2(X1,X4,X5)
                | ~ r2_lattice3(X1,X0,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & r2_lattice3(X1,X0,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ! [X2] :
            ( ~ sP0(X2,X0,X1)
            | ? [X5] :
                ( ~ r1_orders_2(X0,X2,X5)
                & r2_lattice3(X0,X1,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP0(X2,X0,X1)
            & ! [X5] :
                ( r1_orders_2(X0,X2,X5)
                | ~ r2_lattice3(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f548,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | k1_yellow_0(sK5,sK7) = sK10(X0,sK6,sK7) ) ),
    inference(duplicate_literal_removal,[],[f545])).

fof(f545,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP0(X0,sK6,sK7)
      | k1_yellow_0(sK5,sK7) = sK10(X0,sK6,sK7) ) ),
    inference(resolution,[],[f544,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ sP3(sK10(X0,sK6,X1),sK5,sK7)
      | sP0(X0,sK6,X1)
      | k1_yellow_0(sK5,sK7) = sK10(X0,sK6,X1) ) ),
    inference(resolution,[],[f170,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X2,X1,X0)
      | k1_yellow_0(X1,X0) = X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f170,plain,(
    ! [X0,X1] :
      ( sP4(sK7,sK5,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1) ) ),
    inference(resolution,[],[f162,f138])).

fof(f162,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK10(X2,sK6,X3),u1_struct_0(sK5))
      | sP0(X2,sK6,X3) ) ),
    inference(resolution,[],[f158,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK10(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,sK10(X0,X1,X2),X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,sK10(X0,X1,X2))
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,X5,sK11(X1,X2,X5))
              & r2_lattice3(X1,X2,sK11(X1,X2,X5))
              & m1_subset_1(sK11(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X3,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK10(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,sK10(X0,X1,X2),X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_lattice3(X1,X2,sK10(X0,X1,X2))
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X5,X6)
          & r2_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X5,sK11(X1,X2,X5))
        & r2_lattice3(X1,X2,sK11(X1,X2,X5))
        & m1_subset_1(sK11(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X3,X4)
                | ~ r2_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X5,X6)
                & r2_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X3,X4)
                | ~ r2_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f544,plain,(
    ! [X0] :
      ( sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | sP0(X0,sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f543,f249])).

fof(f249,plain,(
    ! [X1] :
      ( r2_lattice3(sK5,sK7,sK10(X1,sK6,sK7))
      | sP0(X1,sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f244,f95])).

fof(f244,plain,(
    ! [X1] :
      ( r2_lattice3(sK5,sK7,sK10(X1,sK6,sK7))
      | ~ m1_subset_1(sK10(X1,sK6,sK7),u1_struct_0(sK6))
      | sP0(X1,sK6,sK7) ) ),
    inference(resolution,[],[f241,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK10(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f543,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r2_lattice3(sK5,sK7,sK10(X0,sK6,sK7)) ) ),
    inference(duplicate_literal_removal,[],[f542])).

fof(f542,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r2_lattice3(sK5,sK7,sK10(X0,sK6,sK7))
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r2_lattice3(sK5,sK7,sK10(X0,sK6,sK7)) ) ),
    inference(resolution,[],[f336,f105])).

fof(f336,plain,(
    ! [X10,X9] :
      ( ~ r2_lattice3(sK5,sK7,sK12(sK10(X9,sK6,sK7),sK5,X10))
      | sP0(X9,sK6,sK7)
      | sP3(sK10(X9,sK6,sK7),sK5,X10)
      | ~ r2_lattice3(sK5,X10,sK10(X9,sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f329,f104])).

fof(f329,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(sK12(sK10(X9,sK6,sK7),sK5,X10),u1_struct_0(sK5))
      | sP0(X9,sK6,sK7)
      | ~ r2_lattice3(sK5,sK7,sK12(sK10(X9,sK6,sK7),sK5,X10))
      | sP3(sK10(X9,sK6,sK7),sK5,X10)
      | ~ r2_lattice3(sK5,X10,sK10(X9,sK6,sK7)) ) ),
    inference(resolution,[],[f323,f106])).

fof(f323,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK5,sK10(X0,sK6,sK7),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | sP0(X0,sK6,sK7)
      | ~ r2_lattice3(sK5,sK7,X1) ) ),
    inference(subsumption_resolution,[],[f321,f162])).

fof(f321,plain,(
    ! [X0,X1] :
      ( sP0(X0,sK6,sK7)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(sK10(X0,sK6,sK7),u1_struct_0(sK5))
      | r1_orders_2(sK5,sK10(X0,sK6,sK7),X1)
      | ~ r2_lattice3(sK5,sK7,X1) ) ),
    inference(resolution,[],[f320,f258])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK5,X0,k1_yellow_0(sK5,sK7))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1)
      | ~ r2_lattice3(sK5,sK7,X1) ) ),
    inference(subsumption_resolution,[],[f257,f159])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK5,X0,k1_yellow_0(sK5,sK7))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1)
      | ~ r2_lattice3(sK5,sK7,X1) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK5,X0,k1_yellow_0(sK5,sK7))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ r2_lattice3(sK5,sK7,X1) ) ),
    inference(resolution,[],[f253,f150])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK5,X0,X1)
      | ~ r1_orders_2(sK5,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | r1_orders_2(sK5,X2,X1) ) ),
    inference(subsumption_resolution,[],[f252,f72])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK5,X0,X1)
      | ~ r1_orders_2(sK5,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5)
      | r1_orders_2(sK5,X2,X1) ) ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f320,plain,(
    ! [X0] :
      ( r1_orders_2(sK5,sK10(X0,sK6,sK7),k1_yellow_0(sK5,sK7))
      | sP0(X0,sK6,sK7) ) ),
    inference(resolution,[],[f319,f145])).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK5,X1,k1_yellow_0(sK5,sK7))
      | r1_orders_2(sK5,sK10(X0,sK6,X1),k1_yellow_0(sK5,sK7))
      | sP0(X0,sK6,X1) ) ),
    inference(resolution,[],[f313,f280])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK6,X1,k1_yellow_0(sK5,sK7))
      | sP0(X0,sK6,X1)
      | r1_orders_2(sK5,sK10(X0,sK6,X1),k1_yellow_0(sK5,sK7)) ) ),
    inference(resolution,[],[f312,f130])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_orders_2(sK5,sK10(X1,sK6,X2),X0)
      | sP0(X1,sK6,X2)
      | ~ r2_lattice3(sK6,X2,X0) ) ),
    inference(subsumption_resolution,[],[f311,f95])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(sK10(X1,sK6,X2),u1_struct_0(sK6))
      | r1_orders_2(sK5,sK10(X1,sK6,X2),X0)
      | sP0(X1,sK6,X2)
      | ~ r2_lattice3(sK6,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(sK10(X1,sK6,X2),u1_struct_0(sK6))
      | r1_orders_2(sK5,sK10(X1,sK6,X2),X0)
      | sP0(X1,sK6,X2)
      | ~ r2_lattice3(sK6,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f309,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X1,sK10(X0,X1,X2),X4)
      | sP0(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f308,f158])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f307,f158])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f306,f72])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f119,f75])).

fof(f119,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

fof(f1156,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f1154,f548])).

fof(f1204,plain,
    ( k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7)
    | k1_yellow_0(sK5,sK7) = k1_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f1203,f453])).

fof(f1203,plain,
    ( k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7)
    | ~ sP3(k1_yellow_0(sK5,sK7),sK6,sK7)
    | k1_yellow_0(sK5,sK7) = k1_yellow_0(sK6,sK7) ),
    inference(resolution,[],[f1189,f101])).

fof(f1189,plain,
    ( sP4(sK7,sK6,k1_yellow_0(sK5,sK7))
    | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f1179,f130])).

fof(f1179,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK6))
      | sP4(sK7,sK6,X8)
      | k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f1178,f132])).

fof(f1178,plain,(
    ! [X8] :
      ( k1_yellow_0(sK5,sK7) = sK10(k1_yellow_0(sK5,sK7),sK6,sK7)
      | sP4(sK7,sK6,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(resolution,[],[f1169,f107])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sK10(X0,X1,X2) != X0
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1154,plain,
    ( ~ sP0(k1_yellow_0(sK5,sK7),sK6,sK7)
    | ~ m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f1153,f130])).

fof(f1153,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ sP0(k1_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f1152,f455])).

fof(f1152,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ sP0(k1_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(duplicate_literal_removal,[],[f1151])).

fof(f1151,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ sP0(k1_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7))
    | ~ sP0(k1_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f415,f247])).

fof(f247,plain,(
    ! [X0] :
      ( r2_lattice3(sK5,sK7,sK8(sK7,sK6,X0))
      | ~ sP0(X0,sK6,sK7)
      | sP1(sK7,sK6)
      | ~ r2_lattice3(sK6,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f242,f89])).

fof(f242,plain,(
    ! [X0] :
      ( r2_lattice3(sK5,sK7,sK8(sK7,sK6,X0))
      | ~ m1_subset_1(sK8(sK7,sK6,X0),u1_struct_0(sK6))
      | ~ sP0(X0,sK6,sK7)
      | sP1(sK7,sK6)
      | ~ r2_lattice3(sK6,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f241,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X0,sK8(X0,X1,X2))
      | ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | ~ r2_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f415,plain,(
    ! [X2] :
      ( ~ r2_lattice3(sK5,sK7,sK8(X2,sK6,k1_yellow_0(sK5,sK7)))
      | ~ m1_subset_1(sK8(X2,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
      | ~ sP0(k1_yellow_0(sK5,sK7),sK6,X2)
      | sP1(X2,sK6)
      | ~ r2_lattice3(sK6,X2,k1_yellow_0(sK5,sK7)) ) ),
    inference(subsumption_resolution,[],[f410,f130])).

fof(f410,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK8(X2,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
      | ~ r2_lattice3(sK5,sK7,sK8(X2,sK6,k1_yellow_0(sK5,sK7)))
      | ~ sP0(k1_yellow_0(sK5,sK7),sK6,X2)
      | sP1(X2,sK6)
      | ~ r2_lattice3(sK6,X2,k1_yellow_0(sK5,sK7))
      | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f401,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X2,sK8(X0,X1,X2))
      | ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | ~ r2_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1288,plain,
    ( sP1(sK7,sK6)
    | m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f1287,f130])).

fof(f1287,plain,
    ( sP1(sK7,sK6)
    | m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f1286,f455])).

fof(f1286,plain,
    ( sP1(sK7,sK6)
    | m1_subset_1(sK8(sK7,sK6,k1_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,sK7,k1_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f1280,f89])).

fof(f79,plain,
    ( ~ r1_yellow_0(sK6,sK7)
    | k1_yellow_0(sK5,sK7) != k1_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f1324,plain,(
    k1_yellow_0(sK5,sK7) = k1_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f1323,f453])).

fof(f1323,plain,
    ( ~ sP3(k1_yellow_0(sK5,sK7),sK6,sK7)
    | k1_yellow_0(sK5,sK7) = k1_yellow_0(sK6,sK7) ),
    inference(resolution,[],[f1314,f101])).

fof(f1314,plain,(
    sP4(sK7,sK6,k1_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f1309,f130])).

fof(f1309,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK6))
      | sP4(sK7,sK6,X7) ) ),
    inference(subsumption_resolution,[],[f1308,f132])).

fof(f1308,plain,(
    ! [X7] :
      ( sP4(sK7,sK6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(resolution,[],[f1300,f107])).

%------------------------------------------------------------------------------
