%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t87_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 143 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 ( 900 expanded)
%              Number of equality atoms :   48 ( 156 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1292,plain,(
    $false ),
    inference(global_subsumption,[],[f382,f1291])).

fof(f1291,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1290,f106])).

fof(f106,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t87_orders_2.p',dt_o_0_0_xboole_0)).

fof(f1290,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f106,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t87_orders_2.p',t6_boole)).

fof(f382,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f107,f226])).

fof(f226,plain,(
    k1_xboole_0 = k1_tarski(k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f173,f155])).

fof(f155,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
      | k1_xboole_0 = X1 ) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f112,f105])).

fof(f105,plain,(
    k3_tarski(k4_orders_2(sK0,sK1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
    ( k3_tarski(k4_orders_2(sK0,sK1)) = k1_xboole_0
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f81,f80])).

fof(f80,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_tarski(k4_orders_2(X0,X1)) = k1_xboole_0
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_tarski(k4_orders_2(sK0,X1)) = k1_xboole_0
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k3_tarski(k4_orders_2(X0,X1)) = k1_xboole_0
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k3_tarski(k4_orders_2(X0,sK1)) = k1_xboole_0
        & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_tarski(k4_orders_2(X0,X1)) = k1_xboole_0
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_tarski(k4_orders_2(X0,X1)) = k1_xboole_0
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k3_tarski(k4_orders_2(X0,X1)) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k3_tarski(k4_orders_2(X0,X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t87_orders_2.p',t87_orders_2)).

fof(f112,plain,(
    ! [X2,X0] :
      ( k3_tarski(X0) != k1_xboole_0
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k3_tarski(X0) = k1_xboole_0 )
      & ( k3_tarski(X0) != k1_xboole_0
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k3_tarski(X0) = k1_xboole_0 )
      & ( k3_tarski(X0) != k1_xboole_0
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k3_tarski(X0) != k1_xboole_0 )
      & ~ ( k3_tarski(X0) = k1_xboole_0
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k3_tarski(X0) != k1_xboole_0 )
      & ~ ( k3_tarski(X0) = k1_xboole_0
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t87_orders_2.p',t91_orders_1)).

fof(f173,plain,(
    r2_hidden(k1_tarski(k1_funct_1(sK1,u1_struct_0(sK0))),k4_orders_2(sK0,sK1)) ),
    inference(global_subsumption,[],[f99,f100,f101,f102,f103,f104,f170])).

fof(f170,plain,
    ( r2_hidden(k1_tarski(k1_funct_1(sK1,u1_struct_0(sK0))),k4_orders_2(sK0,sK1))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f152,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1)
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1)
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t87_orders_2.p',t78_orders_2)).

fof(f152,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | r2_hidden(X1,k4_orders_2(sK0,sK1)) ) ),
    inference(global_subsumption,[],[f99,f100,f101,f102,f103,f150])).

fof(f150,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | r2_hidden(X1,k4_orders_2(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f104,f147])).

fof(f147,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X4,X0,X1)
      | r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK4(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK4(X0,X1,X2),X0,X1)
                    | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f88,f89])).

fof(f89,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK4(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( m2_orders_2(sK4(X0,X1,X2),X0,X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t87_orders_2.p',d17_orders_2)).

fof(f104,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f103,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f102,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f101,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f100,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f99,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f107,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t87_orders_2.p',fc2_xboole_0)).
%------------------------------------------------------------------------------
