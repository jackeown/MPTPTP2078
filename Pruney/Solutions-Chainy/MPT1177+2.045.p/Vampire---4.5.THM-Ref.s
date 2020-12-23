%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 (5681 expanded)
%              Number of leaves         :   14 (2151 expanded)
%              Depth                    :   26
%              Number of atoms          :  809 (60737 expanded)
%              Number of equality atoms :   67 ( 373 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f306,f46,f306,f156])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
      | ~ m2_orders_2(k1_xboole_0,sK0,X0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f155,f111])).

fof(f111,plain,(
    ! [X17,X18] :
      ( ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X17,sK0,X18)
      | v6_orders_2(X17,sK0) ) ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f110,plain,(
    ! [X17,X18] :
      ( ~ m2_orders_2(X17,sK0,X18)
      | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0)))
      | v6_orders_2(X17,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f42,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f109,plain,(
    ! [X17,X18] :
      ( ~ m2_orders_2(X17,sK0,X18)
      | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0)))
      | v6_orders_2(X17,sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f43])).

fof(f43,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,(
    ! [X17,X18] :
      ( ~ m2_orders_2(X17,sK0,X18)
      | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0)))
      | v6_orders_2(X17,sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f44,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X17,X18] :
      ( ~ m2_orders_2(X17,sK0,X18)
      | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0)))
      | v6_orders_2(X17,sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | v6_orders_2(X2,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
      | ~ m2_orders_2(k1_xboole_0,sK0,X0)
      | ~ v6_orders_2(k1_xboole_0,sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f154,f41])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
      | ~ m2_orders_2(k1_xboole_0,sK0,X0)
      | ~ v6_orders_2(k1_xboole_0,sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f42])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
      | ~ m2_orders_2(k1_xboole_0,sK0,X0)
      | ~ v6_orders_2(k1_xboole_0,sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f43])).

fof(f152,plain,(
    ! [X0] :
      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
      | ~ m2_orders_2(k1_xboole_0,sK0,X0)
      | ~ v6_orders_2(k1_xboole_0,sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f44])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
      | ~ m2_orders_2(k1_xboole_0,sK0,X0)
      | ~ v6_orders_2(k1_xboole_0,sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
      | ~ m2_orders_2(k1_xboole_0,sK0,X0)
      | ~ v6_orders_2(k1_xboole_0,sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f139,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2))))
                    & r2_hidden(sK4(X0,X1,X2),X2)
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2))))
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

fof(f139,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f115,f46])).

fof(f115,plain,(
    ! [X19,X20] :
      ( ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X19,sK0,X20)
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f114,f41])).

fof(f114,plain,(
    ! [X19,X20] :
      ( ~ m2_orders_2(X19,sK0,X20)
      | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f113,plain,(
    ! [X19,X20] :
      ( ~ m2_orders_2(X19,sK0,X20)
      | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f43])).

fof(f112,plain,(
    ! [X19,X20] :
      ( ~ m2_orders_2(X19,sK0,X20)
      | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f78,plain,(
    ! [X19,X20] :
      ( ~ m2_orders_2(X19,sK0,X20)
      | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f306,plain,(
    m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(backward_demodulation,[],[f47,f305])).

fof(f305,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f271,f304])).

fof(f304,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f303,f297])).

fof(f297,plain,(
    m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f296,f69])).

fof(f69,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f296,plain,
    ( r2_xboole_0(sK2,sK2)
    | m1_orders_2(sK2,sK0,sK2) ),
    inference(forward_demodulation,[],[f273,f271])).

fof(f273,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | r2_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f49,f271])).

fof(f49,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f303,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f302,f271])).

fof(f302,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f289,f69])).

fof(f289,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f197,f271])).

fof(f197,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f195,f49])).

fof(f195,plain,(
    ! [X6] :
      ( ~ m1_orders_2(sK2,sK0,X6)
      | ~ m1_orders_2(X6,sK0,sK2)
      | k1_xboole_0 = X6 ) ),
    inference(subsumption_resolution,[],[f190,f144])).

fof(f144,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X0,sK0,sK2) ) ),
    inference(resolution,[],[f119,f122])).

fof(f122,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f47,f46,f62])).

fof(f119,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X21,sK0,X22)
      | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f118,plain,(
    ! [X21,X22] :
      ( ~ m1_orders_2(X21,sK0,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,(
    ! [X21,X22] :
      ( ~ m1_orders_2(X21,sK0,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f116,plain,(
    ! [X21,X22] :
      ( ~ m1_orders_2(X21,sK0,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f79,plain,(
    ! [X21,X22] :
      ( ~ m1_orders_2(X21,sK0,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f190,plain,(
    ! [X6] :
      ( k1_xboole_0 = X6
      | ~ m1_orders_2(X6,sK0,sK2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(sK2,sK0,X6) ) ),
    inference(resolution,[],[f107,f122])).

fof(f107,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X15
      | ~ m1_orders_2(X15,sK0,X16)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X16,sK0,X15) ) ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f106,plain,(
    ! [X15,X16] :
      ( ~ m1_orders_2(X15,sK0,X16)
      | k1_xboole_0 = X15
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X16,sK0,X15)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f105,f42])).

fof(f105,plain,(
    ! [X15,X16] :
      ( ~ m1_orders_2(X15,sK0,X16)
      | k1_xboole_0 = X15
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X16,sK0,X15)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f104,plain,(
    ! [X15,X16] :
      ( ~ m1_orders_2(X15,sK0,X16)
      | k1_xboole_0 = X15
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X16,sK0,X15)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f76,f44])).

fof(f76,plain,(
    ! [X15,X16] :
      ( ~ m1_orders_2(X15,sK0,X16)
      | k1_xboole_0 = X15
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X16,sK0,X15)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f271,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f270,f136])).

fof(f136,plain,
    ( r2_xboole_0(sK2,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f130,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f130,plain,(
    r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f129,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f129,plain,
    ( r1_tarski(sK2,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f128,f49])).

fof(f128,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK3)
      | r1_tarski(X1,sK3) ) ),
    inference(resolution,[],[f103,f123])).

fof(f123,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f48,f46,f62])).

fof(f48,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X13,sK0,X14)
      | r1_tarski(X13,X14) ) ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X14,X13] :
      ( ~ m1_orders_2(X13,sK0,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X13,X14)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f42])).

fof(f101,plain,(
    ! [X14,X13] :
      ( ~ m1_orders_2(X13,sK0,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X13,X14)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f43])).

fof(f100,plain,(
    ! [X14,X13] :
      ( ~ m1_orders_2(X13,sK0,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X13,X14)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f75,f44])).

fof(f75,plain,(
    ! [X14,X13] :
      ( ~ m1_orders_2(X13,sK0,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X13,X14)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X2,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f270,plain,
    ( sK2 = sK3
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f269,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f269,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f256,f48])).

fof(f256,plain,
    ( sK2 = sK3
    | ~ m2_orders_2(sK3,sK0,sK1)
    | r1_tarski(sK3,sK2)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f246,f50])).

fof(f50,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f246,plain,(
    ! [X6] :
      ( m1_orders_2(sK2,sK0,X6)
      | sK2 = X6
      | ~ m2_orders_2(X6,sK0,sK1)
      | r1_tarski(X6,sK2) ) ),
    inference(resolution,[],[f230,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f103,f122])).

fof(f230,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | m1_orders_2(X0,sK0,sK2)
      | sK2 = X0
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f199,f47])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | X0 = X1
      | m1_orders_2(X0,sK0,X1)
      | m1_orders_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f87,f46])).

fof(f87,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,X5)
      | ~ m2_orders_2(X4,sK0,X5)
      | m1_orders_2(X3,sK0,X4)
      | m1_orders_2(X4,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f86,plain,(
    ! [X4,X5,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,X5)
      | ~ m2_orders_2(X4,sK0,X5)
      | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
      | m1_orders_2(X4,sK0,X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,(
    ! [X4,X5,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,X5)
      | ~ m2_orders_2(X4,sK0,X5)
      | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
      | m1_orders_2(X4,sK0,X3)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,(
    ! [X4,X5,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,X5)
      | ~ m2_orders_2(X4,sK0,X5)
      | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
      | m1_orders_2(X4,sK0,X3)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f71,f44])).

fof(f71,plain,(
    ! [X4,X5,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,X5)
      | ~ m2_orders_2(X4,sK0,X5)
      | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
      | m1_orders_2(X4,sK0,X3)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X2,X0,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f47,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (31852)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (31846)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31860)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (31846)Refutation not found, incomplete strategy% (31846)------------------------------
% 0.21/0.48  % (31846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31846)Memory used [KB]: 10618
% 0.21/0.48  % (31846)Time elapsed: 0.038 s
% 0.21/0.48  % (31846)------------------------------
% 0.21/0.48  % (31846)------------------------------
% 0.21/0.51  % (31860)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f306,f46,f306,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f155,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X17,X18] : (~m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X17,sK0,X18) | v6_orders_2(X17,sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f31,f30,f29,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X17,X18] : (~m2_orders_2(X17,sK0,X18) | ~m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0))) | v6_orders_2(X17,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v3_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X17,X18] : (~m2_orders_2(X17,sK0,X18) | ~m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0))) | v6_orders_2(X17,sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v4_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X17,X18] : (~m2_orders_2(X17,sK0,X18) | ~m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0))) | v6_orders_2(X17,sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f77,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    v5_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X17,X18] : (~m2_orders_2(X17,sK0,X18) | ~m1_orders_1(X18,k1_orders_1(u1_struct_0(sK0))) | v6_orders_2(X17,sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f45,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v6_orders_2(X2,X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    l1_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f154,f41])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f42])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f43])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f151,f44])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f45])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f139,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2)))) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2)))) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f115,f46])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X19,X20] : (~m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X19,sK0,X20) | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f114,f41])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X19,X20] : (~m2_orders_2(X19,sK0,X20) | ~m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f42])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X19,X20] : (~m2_orders_2(X19,sK0,X20) | ~m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f43])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X19,X20] : (~m2_orders_2(X19,sK0,X20) | ~m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f44])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X19,X20] : (~m2_orders_2(X19,sK0,X20) | ~m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f45,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.51    inference(backward_demodulation,[],[f47,f305])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    k1_xboole_0 = sK2),
% 0.21/0.51    inference(backward_demodulation,[],[f271,f304])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    k1_xboole_0 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f303,f297])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f296,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    r2_xboole_0(sK2,sK2) | m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f273,f271])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    m1_orders_2(sK2,sK0,sK2) | r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(backward_demodulation,[],[f49,f271])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    ~m1_orders_2(sK2,sK0,sK2) | k1_xboole_0 = sK3),
% 0.21/0.51    inference(forward_demodulation,[],[f302,f271])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f289,f69])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    r2_xboole_0(sK2,sK2) | ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3),
% 0.21/0.51    inference(backward_demodulation,[],[f197,f271])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f195,f49])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X6] : (~m1_orders_2(sK2,sK0,X6) | ~m1_orders_2(X6,sK0,sK2) | k1_xboole_0 = X6) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f190,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,sK2)) )),
% 0.21/0.51    inference(resolution,[],[f119,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f47,f46,f62])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X21,X22] : (~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X21,sK0,X22) | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f41])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X21,X22] : (~m1_orders_2(X21,sK0,X22) | ~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f42])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X21,X22] : (~m1_orders_2(X21,sK0,X22) | ~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f116,f43])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X21,X22] : (~m1_orders_2(X21,sK0,X22) | ~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f79,f44])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X21,X22] : (~m1_orders_2(X21,sK0,X22) | ~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f45,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ( ! [X6] : (k1_xboole_0 = X6 | ~m1_orders_2(X6,sK0,sK2) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(sK2,sK0,X6)) )),
% 0.21/0.51    inference(resolution,[],[f107,f122])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X15,X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X15 | ~m1_orders_2(X15,sK0,X16) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X16,sK0,X15)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f106,f41])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X15,X16] : (~m1_orders_2(X15,sK0,X16) | k1_xboole_0 = X15 | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X16,sK0,X15) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f105,f42])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X15,X16] : (~m1_orders_2(X15,sK0,X16) | k1_xboole_0 = X15 | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X16,sK0,X15) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f43])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X15,X16] : (~m1_orders_2(X15,sK0,X16) | k1_xboole_0 = X15 | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X16,sK0,X15) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f76,f44])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X15,X16] : (~m1_orders_2(X15,sK0,X16) | k1_xboole_0 = X15 | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X16,sK0,X15) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f45,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f270,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    r2_xboole_0(sK2,sK3) | sK2 = sK3),
% 0.21/0.51    inference(resolution,[],[f130,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    r1_tarski(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    r1_tarski(sK2,sK3) | r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f128,f49])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_orders_2(X1,sK0,sK3) | r1_tarski(X1,sK3)) )),
% 0.21/0.51    inference(resolution,[],[f103,f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f41,f42,f43,f44,f45,f48,f46,f62])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    m2_orders_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X14,X13] : (~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X13,sK0,X14) | r1_tarski(X13,X14)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f41])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X14,X13] : (~m1_orders_2(X13,sK0,X14) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X13,X14) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f42])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X14,X13] : (~m1_orders_2(X13,sK0,X14) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X13,X14) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f43])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X14,X13] : (~m1_orders_2(X13,sK0,X14) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X13,X14) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f44])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X14,X13] : (~m1_orders_2(X13,sK0,X14) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X13,X14) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f45,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X2,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    sK2 = sK3 | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f269,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    sK2 = sK3 | r1_tarski(sK3,sK2) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f256,f48])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    sK2 = sK3 | ~m2_orders_2(sK3,sK0,sK1) | r1_tarski(sK3,sK2) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f246,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X6] : (m1_orders_2(sK2,sK0,X6) | sK2 = X6 | ~m2_orders_2(X6,sK0,sK1) | r1_tarski(X6,sK2)) )),
% 0.21/0.51    inference(resolution,[],[f230,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 0.21/0.51    inference(resolution,[],[f103,f122])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | m1_orders_2(X0,sK0,sK2) | sK2 = X0 | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f199,f47])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | X0 = X1 | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f87,f46])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | X3 = X4 | ~m2_orders_2(X3,sK0,X5) | ~m2_orders_2(X4,sK0,X5) | m1_orders_2(X3,sK0,X4) | m1_orders_2(X4,sK0,X3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f41])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,X5) | ~m2_orders_2(X4,sK0,X5) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X4,sK0,X3) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f42])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,X5) | ~m2_orders_2(X4,sK0,X5) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X4,sK0,X3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f43])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,X5) | ~m2_orders_2(X4,sK0,X5) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X4,sK0,X3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f44])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,X5) | ~m2_orders_2(X4,sK0,X5) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X4,sK0,X3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f45,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X2,X0,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    m2_orders_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31860)------------------------------
% 0.21/0.51  % (31860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31860)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (31860)Memory used [KB]: 6396
% 0.21/0.51  % (31860)Time elapsed: 0.084 s
% 0.21/0.51  % (31860)------------------------------
% 0.21/0.51  % (31860)------------------------------
% 0.21/0.51  % (31849)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (31844)Success in time 0.148 s
%------------------------------------------------------------------------------
