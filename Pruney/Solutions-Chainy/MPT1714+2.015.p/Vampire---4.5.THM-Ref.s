%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 865 expanded)
%              Number of leaves         :   20 ( 328 expanded)
%              Depth                    :   28
%              Number of atoms          :  394 (8434 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(subsumption_resolution,[],[f180,f175])).

fof(f175,plain,(
    r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f174,f85])).

fof(f85,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f82,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f78,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f78,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f47])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f174,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f171,f87])).

fof(f87,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f84,f59])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f80,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f171,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f170,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f170,plain,(
    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f169,f113])).

fof(f113,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f112,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f91,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f71,f55])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f91,plain,(
    ! [X0] : v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f90,f56])).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f67,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(resolution,[],[f74,f56])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f69,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f169,plain,(
    r1_xboole_0(u1_struct_0(sK1),k5_xboole_0(u1_struct_0(sK3),k1_xboole_0)) ),
    inference(superposition,[],[f166,f131])).

fof(f131,plain,(
    k1_xboole_0 = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f123,f88])).

fof(f123,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    inference(resolution,[],[f119,f90])).

fof(f119,plain,(
    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f118,f87])).

fof(f118,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f115,f86])).

fof(f86,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f83,f59])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f79,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f115,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3) ),
    inference(resolution,[],[f57,f109])).

fof(f109,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f108,f86])).

fof(f108,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f107,f87])).

fof(f107,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f106,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f106,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f105,f87])).

fof(f105,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f104,f86])).

fof(f104,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f166,plain,(
    ! [X1] : r1_xboole_0(u1_struct_0(sK1),k5_xboole_0(X1,k3_xboole_0(X1,u1_struct_0(sK2)))) ),
    inference(resolution,[],[f164,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f164,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f163,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f163,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f162,f45])).

fof(f162,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f161,f47])).

fof(f161,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f149,f49])).

fof(f149,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(sK2,X3)
      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK1,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f62,f52])).

fof(f52,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f180,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f179,f53])).

fof(f53,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f179,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f178,f85])).

fof(f178,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f177,f87])).

fof(f177,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f175,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (11540)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % (11540)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f183,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f180,f175])).
% 0.20/0.44  fof(f175,plain,(
% 0.20/0.44    r1_tsep_1(sK1,sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f174,f85])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    l1_struct_0(sK1)),
% 0.20/0.44    inference(resolution,[],[f82,f59])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    l1_pre_topc(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f78,f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    l1_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f32,f31,f30,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.44    inference(negated_conjecture,[],[f14])).
% 0.20/0.44  fof(f14,conjecture,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.44    inference(resolution,[],[f60,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    m1_pre_topc(sK1,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.44  fof(f174,plain,(
% 0.20/0.44    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f171,f87])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    l1_struct_0(sK3)),
% 0.20/0.44    inference(resolution,[],[f84,f59])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    l1_pre_topc(sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f80,f45])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.20/0.44    inference(resolution,[],[f60,f51])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    m1_pre_topc(sK3,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f171,plain,(
% 0.20/0.44    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1)),
% 0.20/0.44    inference(resolution,[],[f170,f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.20/0.44  fof(f170,plain,(
% 0.20/0.44    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.20/0.44    inference(forward_demodulation,[],[f169,f113])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(forward_demodulation,[],[f112,f92])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(resolution,[],[f91,f88])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.44    inference(resolution,[],[f71,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.44    inference(resolution,[],[f90,f56])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(resolution,[],[f67,f64])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.44    inference(rectify,[],[f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.44    inference(nnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(rectify,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.44  fof(f112,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.44    inference(resolution,[],[f74,f56])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(definition_unfolding,[],[f69,f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.44  fof(f169,plain,(
% 0.20/0.44    r1_xboole_0(u1_struct_0(sK1),k5_xboole_0(u1_struct_0(sK3),k1_xboole_0))),
% 0.20/0.44    inference(superposition,[],[f166,f131])).
% 0.20/0.44  fof(f131,plain,(
% 0.20/0.44    k1_xboole_0 = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.44    inference(resolution,[],[f123,f88])).
% 0.20/0.44  fof(f123,plain,(
% 0.20/0.44    v1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)))),
% 0.20/0.44    inference(resolution,[],[f119,f90])).
% 0.20/0.44  fof(f119,plain,(
% 0.20/0.44    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.44    inference(subsumption_resolution,[],[f118,f87])).
% 0.20/0.44  fof(f118,plain,(
% 0.20/0.44    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f115,f86])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    l1_struct_0(sK2)),
% 0.20/0.44    inference(resolution,[],[f83,f59])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    l1_pre_topc(sK2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f79,f45])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.44    inference(resolution,[],[f60,f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    m1_pre_topc(sK2,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3)),
% 0.20/0.44    inference(resolution,[],[f57,f109])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    r1_tsep_1(sK3,sK2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f108,f86])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    r1_tsep_1(sK3,sK2) | ~l1_struct_0(sK2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f107,f87])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    r1_tsep_1(sK3,sK2) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.44    inference(resolution,[],[f106,f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    r1_tsep_1(sK2,sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f105,f87])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f104,f86])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3)),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f103])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.20/0.44    inference(resolution,[],[f68,f54])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f34])).
% 0.20/0.44  fof(f166,plain,(
% 0.20/0.44    ( ! [X1] : (r1_xboole_0(u1_struct_0(sK1),k5_xboole_0(X1,k3_xboole_0(X1,u1_struct_0(sK2))))) )),
% 0.20/0.44    inference(resolution,[],[f164,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f72,f65])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.44  fof(f164,plain,(
% 0.20/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.44    inference(subsumption_resolution,[],[f163,f44])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    v2_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f163,plain,(
% 0.20/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~v2_pre_topc(sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f162,f45])).
% 0.20/0.44  fof(f162,plain,(
% 0.20/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f161,f47])).
% 0.20/0.44  fof(f161,plain,(
% 0.20/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.44    inference(resolution,[],[f149,f49])).
% 0.20/0.44  fof(f149,plain,(
% 0.20/0.44    ( ! [X3] : (~m1_pre_topc(sK2,X3) | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~m1_pre_topc(sK1,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 0.20/0.44    inference(resolution,[],[f62,f52])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    m1_pre_topc(sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.44  fof(f180,plain,(
% 0.20/0.44    ~r1_tsep_1(sK1,sK3)),
% 0.20/0.44    inference(resolution,[],[f179,f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f179,plain,(
% 0.20/0.44    r1_tsep_1(sK3,sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f178,f85])).
% 0.20/0.44  fof(f178,plain,(
% 0.20/0.44    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f177,f87])).
% 0.20/0.44  fof(f177,plain,(
% 0.20/0.44    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1)),
% 0.20/0.44    inference(resolution,[],[f175,f68])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (11540)------------------------------
% 0.20/0.44  % (11540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (11540)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (11540)Memory used [KB]: 1663
% 0.20/0.44  % (11540)Time elapsed: 0.010 s
% 0.20/0.44  % (11540)------------------------------
% 0.20/0.44  % (11540)------------------------------
% 0.20/0.44  % (11523)Success in time 0.08 s
%------------------------------------------------------------------------------
