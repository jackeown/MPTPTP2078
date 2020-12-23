%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1523+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   92 (1353 expanded)
%              Number of leaves         :   11 ( 643 expanded)
%              Depth                    :   37
%              Number of atoms          :  421 (16526 expanded)
%              Number of equality atoms :   84 (3997 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f23])).

fof(f23,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( ~ r2_orders_2(sK1,sK4,sK5)
        & r2_orders_2(sK0,sK2,sK3) )
      | ( ~ r1_orders_2(sK1,sK4,sK5)
        & r1_orders_2(sK0,sK2,sK3) ) )
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f18,f17,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ( ~ r2_orders_2(X1,X4,X5)
                                & r2_orders_2(X0,X2,X3) )
                              | ( ~ r1_orders_2(X1,X4,X5)
                                & r1_orders_2(X0,X2,X3) ) )
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(sK0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(sK0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ( ~ r2_orders_2(X1,X4,X5)
                            & r2_orders_2(sK0,X2,X3) )
                          | ( ~ r1_orders_2(X1,X4,X5)
                            & r1_orders_2(sK0,X2,X3) ) )
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ( ~ r2_orders_2(sK1,X4,X5)
                          & r2_orders_2(sK0,X2,X3) )
                        | ( ~ r1_orders_2(sK1,X4,X5)
                          & r1_orders_2(sK0,X2,X3) ) )
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ( ~ r2_orders_2(sK1,X4,X5)
                        & r2_orders_2(sK0,X2,X3) )
                      | ( ~ r1_orders_2(sK1,X4,X5)
                        & r1_orders_2(sK0,X2,X3) ) )
                    & X3 = X5
                    & X2 = X4
                    & m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ( ~ r2_orders_2(sK1,X4,X5)
                      & r2_orders_2(sK0,sK2,X3) )
                    | ( ~ r1_orders_2(sK1,X4,X5)
                      & r1_orders_2(sK0,sK2,X3) ) )
                  & X3 = X5
                  & sK2 = X4
                  & m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ( ~ r2_orders_2(sK1,X4,X5)
                    & r2_orders_2(sK0,sK2,X3) )
                  | ( ~ r1_orders_2(sK1,X4,X5)
                    & r1_orders_2(sK0,sK2,X3) ) )
                & X3 = X5
                & sK2 = X4
                & m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ( ~ r2_orders_2(sK1,X4,X5)
                  & r2_orders_2(sK0,sK2,sK3) )
                | ( ~ r1_orders_2(sK1,X4,X5)
                  & r1_orders_2(sK0,sK2,sK3) ) )
              & sK3 = X5
              & sK2 = X4
              & m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

% (11165)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f17,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ( ~ r2_orders_2(sK1,X4,X5)
                & r2_orders_2(sK0,sK2,sK3) )
              | ( ~ r1_orders_2(sK1,X4,X5)
                & r1_orders_2(sK0,sK2,sK3) ) )
            & sK3 = X5
            & sK2 = X4
            & m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ( ( ~ r2_orders_2(sK1,sK4,X5)
              & r2_orders_2(sK0,sK2,sK3) )
            | ( ~ r1_orders_2(sK1,sK4,X5)
              & r1_orders_2(sK0,sK2,sK3) ) )
          & sK3 = X5
          & sK2 = sK4
          & m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X5] :
        ( ( ( ~ r2_orders_2(sK1,sK4,X5)
            & r2_orders_2(sK0,sK2,sK3) )
          | ( ~ r1_orders_2(sK1,sK4,X5)
            & r1_orders_2(sK0,sK2,sK3) ) )
        & sK3 = X5
        & sK2 = sK4
        & m1_subset_1(X5,u1_struct_0(sK1)) )
   => ( ( ( ~ r2_orders_2(sK1,sK4,sK5)
          & r2_orders_2(sK0,sK2,sK3) )
        | ( ~ r1_orders_2(sK1,sK4,sK5)
          & r1_orders_2(sK0,sK2,sK3) ) )
      & sK3 = sK5
      & sK2 = sK4
      & m1_subset_1(sK5,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f150,plain,(
    ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f147,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f147,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f143,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f143,plain,(
    r2_orders_2(sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f122,f138])).

fof(f138,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f137,f120])).

fof(f120,plain,(
    ~ r2_orders_2(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f119,f53])).

fof(f53,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r2_orders_2(sK1,sK2,sK3) ),
    inference(forward_demodulation,[],[f50,f30])).

fof(f30,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ r2_orders_2(sK1,sK4,sK3) ),
    inference(backward_demodulation,[],[f49,f30])).

fof(f49,plain,
    ( ~ r2_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK3) ),
    inference(forward_demodulation,[],[f48,f31])).

fof(f31,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,
    ( ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r2_orders_2(sK1,sK4,sK5) ),
    inference(backward_demodulation,[],[f35,f31])).

fof(f35,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ r2_orders_2(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f117,f27])).

fof(f27,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f117,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_orders_2(sK1,sK2,sK3) ),
    inference(resolution,[],[f115,f51])).

fof(f51,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ r2_orders_2(sK1,sK2,sK3) ),
    inference(backward_demodulation,[],[f47,f30])).

fof(f47,plain,
    ( ~ r2_orders_2(sK1,sK4,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f34,f31])).

fof(f34,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f114,f26])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK1,X3,X2)
      | ~ r1_orders_2(sK0,X3,X2) ) ),
    inference(subsumption_resolution,[],[f112,f23])).

fof(f112,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_orders_2(sK1,X3,X2)
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_orders_2(sK1,X3,X2)
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f105,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK1,X2,X3) ) ),
    inference(forward_demodulation,[],[f104,f61])).

fof(f61,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f57,f25])).

fof(f25,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f56,f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r1_orders_2(sK1,X2,X3) ) ),
    inference(forward_demodulation,[],[f103,f61])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r1_orders_2(sK1,X2,X3) ) ),
    inference(forward_demodulation,[],[f102,f80])).

fof(f80,plain,(
    u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK1) = X1 ) ),
    inference(superposition,[],[f75,f63])).

fof(f63,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(backward_demodulation,[],[f25,f61])).

fof(f75,plain,(
    ! [X4,X3] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) != g1_orders_2(X3,X4)
      | u1_orders_2(sK1) = X4 ) ),
    inference(resolution,[],[f43,f68])).

fof(f68,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f67,f24])).

fof(f24,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1) ),
    inference(superposition,[],[f36,f61])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r1_orders_2(sK1,X2,X3) ) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f137,plain,
    ( sK2 = sK3
    | r2_orders_2(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f136,f26])).

fof(f136,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f135,f27])).

fof(f135,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK1,sK2,sK3) ),
    inference(resolution,[],[f133,f128])).

fof(f128,plain,(
    r1_orders_2(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f127,f27])).

fof(f127,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f126,f115])).

fof(f126,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f125,f23])).

fof(f125,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f124,f26])).

fof(f124,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f123,f27])).

fof(f123,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f122,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | X2 = X3
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK1,X2,X3) ) ),
    inference(forward_demodulation,[],[f132,f61])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | X2 = X3
      | ~ r1_orders_2(sK1,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r2_orders_2(sK1,X2,X3) ) ),
    inference(forward_demodulation,[],[f131,f61])).

fof(f131,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r1_orders_2(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r2_orders_2(sK1,X2,X3) ) ),
    inference(resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f122,plain,(
    r2_orders_2(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f121,f52])).

fof(f52,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f46,f30])).

fof(f46,plain,
    ( ~ r1_orders_2(sK1,sK4,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f33,f31])).

fof(f33,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f121,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f118,f27])).

fof(f118,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(resolution,[],[f115,f32])).

fof(f32,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
