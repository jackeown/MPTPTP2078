%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t58_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 100 expanded)
%              Number of leaves         :    5 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 683 expanded)
%              Number of equality atoms :   39 ( 221 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(backward_demodulation,[],[f108,f78])).

fof(f78,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK2)) ),
    inference(backward_demodulation,[],[f59,f60])).

fof(f60,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & m1_yellow_0(sK2,sK0)
    & v4_yellow_0(sK2,sK0)
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & u1_struct_0(X1) = u1_struct_0(X2)
                & m1_yellow_0(X2,X0)
                & v4_yellow_0(X2,X0) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,sK0)
              & v4_yellow_0(X2,sK0) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
            & u1_struct_0(sK1) = u1_struct_0(X2)
            & m1_yellow_0(X2,X0)
            & v4_yellow_0(X2,X0) )
        & m1_yellow_0(sK1,X0)
        & v4_yellow_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
          & u1_struct_0(X1) = u1_struct_0(X2)
          & m1_yellow_0(X2,X0)
          & v4_yellow_0(X2,X0) )
     => ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
        & u1_struct_0(sK2) = u1_struct_0(X1)
        & m1_yellow_0(sK2,X0)
        & v4_yellow_0(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0) )
           => ! [X2] :
                ( ( m1_yellow_0(X2,X0)
                  & v4_yellow_0(X2,X0) )
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( ( m1_yellow_0(X2,X0)
                & v4_yellow_0(X2,X0) )
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t58_yellow_0.p',t58_yellow_0)).

fof(f59,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f108,plain,(
    u1_orders_2(sK1) = u1_orders_2(sK2) ),
    inference(forward_demodulation,[],[f107,f90])).

fof(f90,plain,(
    u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f89,f54])).

fof(f54,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f88,f56])).

fof(f56,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f55,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t58_yellow_0.p',d14_yellow_0)).

fof(f55,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f106,f59])).

fof(f106,plain,(
    u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f105,f54])).

fof(f105,plain,
    ( u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f104,f58])).

fof(f58,plain,(
    m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,
    ( u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2))
    | ~ m1_yellow_0(sK2,sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f57,f69])).

fof(f57,plain,(
    v4_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
