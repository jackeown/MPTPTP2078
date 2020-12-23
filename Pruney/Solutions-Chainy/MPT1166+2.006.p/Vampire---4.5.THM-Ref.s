%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 (1426 expanded)
%              Number of leaves         :    8 ( 578 expanded)
%              Depth                    :   26
%              Number of atoms          :  538 (14366 expanded)
%              Number of equality atoms :   81 (2011 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(subsumption_resolution,[],[f299,f250])).

fof(f250,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f30,f247])).

fof(f247,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f80,f84,f79,f246])).

fof(f246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK2
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f241,f170])).

fof(f170,plain,
    ( sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f168,f32])).

fof(f32,plain,(
    m1_orders_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    & m1_orders_2(sK1,sK0,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( m1_orders_2(X2,X0,X1)
                & m1_orders_2(X1,X0,X2)
                & k1_xboole_0 != X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,sK0,X1)
              & m1_orders_2(X1,sK0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( m1_orders_2(X2,sK0,X1)
            & m1_orders_2(X1,sK0,X2)
            & k1_xboole_0 != X1
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( m1_orders_2(X2,sK0,sK1)
          & m1_orders_2(sK1,sK0,X2)
          & k1_xboole_0 != sK1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( m1_orders_2(X2,sK0,sK1)
        & m1_orders_2(sK1,sK0,X2)
        & k1_xboole_0 != sK1
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( m1_orders_2(sK2,sK0,sK1)
      & m1_orders_2(sK1,sK0,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f168,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK1,sK0,sK2)
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(resolution,[],[f145,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f145,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = sK2
      | ~ m1_orders_2(X1,sK0,sK2)
      | k3_orders_2(sK0,sK2,sK3(sK0,sK2,X1)) = X1 ) ),
    inference(resolution,[],[f62,f30])).

fof(f62,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X2,sK0,X3)
      | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X2,X3] :
      ( ~ m1_orders_2(X2,sK0,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f60,f25])).

fof(f25,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X3] :
      ( ~ m1_orders_2(X2,sK0,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f59,f26])).

fof(f26,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X2,X3] :
      ( ~ m1_orders_2(X2,sK0,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f50,f27])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X3] :
      ( ~ m1_orders_2(X2,sK0,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
                        & r2_hidden(sK3(X0,X1,X2),X1)
                        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

% (20383)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f241,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)))
      | k1_xboole_0 = sK2
      | r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f239,f32])).

fof(f239,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ m1_orders_2(sK1,sK0,sK2)
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X1,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f227,f30])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,sK2)
      | ~ m1_orders_2(sK1,sK0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f142,f29])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f141,f24])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f25])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f26])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f27])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f28])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f94,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X2,k3_orders_2(sK0,sK2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f74,f30])).

fof(f74,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X9,k3_orders_2(sK0,X10,X11))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f73,f24])).

fof(f73,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k3_orders_2(sK0,X10,X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,X10)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f25])).

fof(f72,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k3_orders_2(sK0,X10,X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,X10)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f71,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k3_orders_2(sK0,X10,X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,X10)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f53,f27])).

% (20366)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f53,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k3_orders_2(sK0,X10,X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,X10)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f9])).

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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f79,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f33,f29,f30,f38])).

fof(f33,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    ~ r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f82,f81])).

% (20377)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f81,plain,(
    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f33,f29,f30,f40])).

fof(f82,plain,(
    ~ r2_hidden(sK3(sK0,sK1,sK2),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f29,f79,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

fof(f80,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f33,f29,f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f299,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f29,f251,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f251,plain,(
    m1_orders_2(sK1,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f32,f247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20371)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (20373)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (20379)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (20374)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (20368)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (20365)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (20365)Refutation not found, incomplete strategy% (20365)------------------------------
% 0.20/0.47  % (20365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (20365)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (20365)Memory used [KB]: 10618
% 0.20/0.47  % (20365)Time elapsed: 0.061 s
% 0.20/0.47  % (20365)------------------------------
% 0.20/0.47  % (20365)------------------------------
% 0.20/0.47  % (20369)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (20372)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (20379)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (20364)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (20380)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (20367)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (20370)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (20364)Refutation not found, incomplete strategy% (20364)------------------------------
% 0.20/0.49  % (20364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20364)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (20364)Memory used [KB]: 6268
% 0.20/0.49  % (20364)Time elapsed: 0.085 s
% 0.20/0.49  % (20364)------------------------------
% 0.20/0.49  % (20364)------------------------------
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f299,f250])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f30,f247])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    k1_xboole_0 = sK2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f80,f84,f79,f246])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK2 | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f245])).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK2) )),
% 0.20/0.49    inference(superposition,[],[f241,f170])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(subsumption_resolution,[],[f168,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    m1_orders_2(sK1,sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ((m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f6])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f4])).
% 0.20/0.49  fof(f4,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~m1_orders_2(sK1,sK0,sK2) | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.20/0.49    inference(resolution,[],[f145,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(X1,sK0,sK2) | k3_orders_2(sK0,sK2,sK3(sK0,sK2,X1)) = X1) )),
% 0.20/0.49    inference(resolution,[],[f62,f30])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X2,sK0,X3) | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f61,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_orders_2(X2,sK0,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2 | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f60,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    v3_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_orders_2(X2,sK0,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f59,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    v4_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_orders_2(X2,sK0,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f50,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_orders_2(X2,sK0,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X3,sK3(sK0,X3,X2)) = X2 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f28,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(rectify,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    l1_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % (20383)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))) | k1_xboole_0 = sK2 | r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f239,f32])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    ( ! [X1] : (r2_hidden(X1,sK2) | ~m1_orders_2(sK1,sK0,sK2) | k1_xboole_0 = sK2 | ~r2_hidden(X1,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f227,f30])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,sK2) | ~m1_orders_2(sK1,sK0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f142,f29])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f141,f24])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f140,f25])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f139,f26])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f138,f27])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f28])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK2,sK3(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK2) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f94,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,k3_orders_2(sK0,sK2,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,sK2)) )),
% 0.20/0.49    inference(resolution,[],[f74,f30])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X9,k3_orders_2(sK0,X10,X11)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,X10)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f73,f24])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_orders_2(sK0,X10,X11)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,X10) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f72,f25])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_orders_2(sK0,X10,X11)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,X10) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f71,f26])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_orders_2(sK0,X10,X11)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,X10) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f53,f27])).
% 0.20/0.49  % (20366)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_orders_2(sK0,X10,X11)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r2_hidden(X9,X10) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f28,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f33,f29,f30,f38])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    m1_orders_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    k1_xboole_0 != sK1),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK1,sK2),sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f82,f81])).
% 0.20/0.49  % (20377)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f33,f29,f30,f40])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK1,sK2),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f29,f79,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f33,f29,f30,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X1,X2),X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f24,f25,f26,f27,f28,f31,f29,f251,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    m1_orders_2(sK1,sK0,k1_xboole_0)),
% 0.20/0.49    inference(backward_demodulation,[],[f32,f247])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (20379)------------------------------
% 0.20/0.49  % (20379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20379)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (20379)Memory used [KB]: 6396
% 0.20/0.49  % (20379)Time elapsed: 0.079 s
% 0.20/0.49  % (20379)------------------------------
% 0.20/0.49  % (20379)------------------------------
% 0.20/0.49  % (20363)Success in time 0.139 s
%------------------------------------------------------------------------------
