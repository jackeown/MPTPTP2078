%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 832 expanded)
%              Number of leaves         :   17 ( 433 expanded)
%              Depth                    :   32
%              Number of atoms          :  439 (9143 expanded)
%              Number of equality atoms :   46 (1958 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(resolution,[],[f128,f71])).

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f46,f48])).

fof(f48,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_orders_2(sK1,sK3,sK4)
    & r1_orders_2(sK2,sK5,sK6)
    & sK4 = sK6
    & sK3 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f33,f32,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_orders_2(X1,X3,X4)
                                & r1_orders_2(X2,X5,X6)
                                & X4 = X6
                                & X3 = X5
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_orders_2(X1,X3,X4)
                            & r1_orders_2(X2,X5,X6)
                            & X4 = X6
                            & X3 = X5
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_orders_2(sK1,X3,X4)
                          & r1_orders_2(X2,X5,X6)
                          & X4 = X6
                          & X3 = X5
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(sK1,X3,X4)
                        & r1_orders_2(X2,X5,X6)
                        & X4 = X6
                        & X3 = X5
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_yellow_6(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(sK1,X3,X4)
                      & r1_orders_2(sK2,X5,X6)
                      & X4 = X6
                      & X3 = X5
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(sK2)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_yellow_6(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(sK1,X3,X4)
                    & r1_orders_2(sK2,X5,X6)
                    & X4 = X6
                    & X3 = X5
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(sK2)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(sK1,sK3,X4)
                  & r1_orders_2(sK2,X5,X6)
                  & X4 = X6
                  & sK3 = X5
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK2)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(sK1,sK3,X4)
                & r1_orders_2(sK2,X5,X6)
                & X4 = X6
                & sK3 = X5
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK2)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(sK1,sK3,sK4)
              & r1_orders_2(sK2,X5,X6)
              & sK4 = X6
              & sK3 = X5
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_orders_2(sK1,sK3,sK4)
            & r1_orders_2(sK2,X5,X6)
            & sK4 = X6
            & sK3 = X5
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK2)) )
   => ( ? [X6] :
          ( ~ r1_orders_2(sK1,sK3,sK4)
          & r1_orders_2(sK2,sK5,X6)
          & sK4 = X6
          & sK3 = sK5
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X6] :
        ( ~ r1_orders_2(sK1,sK3,sK4)
        & r1_orders_2(sK2,sK5,X6)
        & sK4 = X6
        & sK3 = sK5
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ~ r1_orders_2(sK1,sK3,sK4)
      & r1_orders_2(sK2,sK5,sK6)
      & sK4 = sK6
      & sK3 = sK5
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X2,X5,X6)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X2,X5,X6)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).

fof(f46,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f128,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f127,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f47,f49])).

fof(f49,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f127,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f126,f69])).

fof(f69,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f68,f48])).

fof(f68,plain,(
    r1_orders_2(sK2,sK5,sK4) ),
    inference(backward_demodulation,[],[f50,f49])).

fof(f50,plain,(
    r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f125,f80])).

fof(f80,plain,(
    l1_orders_2(sK2) ),
    inference(resolution,[],[f78,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | l1_orders_2(X0) ) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f78,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f76,f43])).

fof(f43,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_yellow_6(X0,sK0,sK1)
      | l1_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f75,f42])).

fof(f42,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,sK0)
      | ~ m1_yellow_6(X0,sK0,X1)
      | l1_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f63,f41])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f125,plain,(
    ! [X2,X1] :
      ( ~ l1_orders_2(sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X1,X2) ) ),
    inference(resolution,[],[f123,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f123,plain,(
    ! [X0] : ~ r2_hidden(X0,u1_orders_2(sK2)) ),
    inference(resolution,[],[f122,f91])).

fof(f91,plain,(
    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(u1_orders_2(sK1))) ),
    inference(resolution,[],[f89,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f89,plain,(
    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) ),
    inference(resolution,[],[f88,f73])).

fof(f73,plain,(
    l1_orders_2(sK1) ),
    inference(resolution,[],[f72,f42])).

fof(f88,plain,
    ( ~ l1_orders_2(sK1)
    | r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) ),
    inference(resolution,[],[f86,f80])).

fof(f86,plain,
    ( ~ l1_orders_2(sK2)
    | r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

% (23525)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f84,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f83,f42])).

fof(f83,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | m1_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f82,f78])).

fof(f82,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | m1_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f77,f43])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_6(X0,sK0,X1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X1,sK0)
      | m1_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_yellow_0(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_orders_2(sK1)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f121,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f121,plain,(
    v1_xboole_0(u1_orders_2(sK1)) ),
    inference(resolution,[],[f120,f51])).

fof(f51,plain,(
    ~ r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f120,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | v1_xboole_0(u1_orders_2(sK1)) ),
    inference(resolution,[],[f119,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f119,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_orders_2(sK1))
    | r1_orders_2(sK1,sK3,sK4) ),
    inference(resolution,[],[f118,f71])).

fof(f118,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK4) ),
    inference(resolution,[],[f117,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f117,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK1,sK3,sK4) ),
    inference(resolution,[],[f116,f70])).

fof(f116,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_orders_2(sK1,sK3,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_orders_2(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(resolution,[],[f115,f69])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | v1_xboole_0(u1_orders_2(sK1))
      | r1_orders_2(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f114,f73])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_orders_2(sK1))
      | r1_orders_2(sK1,X0,X1)
      | ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f113,f80])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | v1_xboole_0(u1_orders_2(sK1))
      | r1_orders_2(sK1,X1,X0)
      | ~ r1_orders_2(sK2,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f98,f95])).

fof(f95,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k4_tarski(X1,X2),u1_orders_2(sK1))
      | ~ r1_orders_2(sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_orders_2(sK2))
      | m1_subset_1(X0,u1_orders_2(sK1)) ) ),
    inference(resolution,[],[f91,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f98,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k4_tarski(X4,X5),u1_orders_2(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_orders_2(X3))
      | r1_orders_2(X3,X4,X5) ) ),
    inference(resolution,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (23521)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.47  % (23517)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (23528)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (23538)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (23526)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (23526)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (23533)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.53  % (23518)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (23519)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  % (23524)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (23524)Refutation not found, incomplete strategy% (23524)------------------------------
% 0.22/0.53  % (23524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23533)Refutation not found, incomplete strategy% (23533)------------------------------
% 0.22/0.53  % (23533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23524)Memory used [KB]: 6140
% 0.22/0.53  % (23533)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  % (23524)Time elapsed: 0.095 s
% 0.22/0.53  % (23524)------------------------------
% 0.22/0.53  % (23524)------------------------------
% 0.22/0.53  
% 0.22/0.53  % (23533)Memory used [KB]: 1535
% 0.22/0.53  % (23533)Time elapsed: 0.095 s
% 0.22/0.53  % (23533)------------------------------
% 0.22/0.53  % (23533)------------------------------
% 0.22/0.54  % (23520)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.54  % (23537)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.54  % (23529)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f128,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.54    inference(forward_demodulation,[],[f46,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    sK3 = sK5),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ((((((~r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK2,sK5,sK6) & sK4 = sK6 & sK3 = sK5 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_yellow_6(sK2,sK0,sK1)) & l1_waybel_0(sK1,sK0)) & l1_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f33,f32,f31,f30,f29,f28,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0)) & l1_struct_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(X2,sK0,sK1)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK1,X3,X4) & r1_orders_2(sK2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(sK2,sK0,sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK1,X3,X4) & r1_orders_2(sK2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK1,sK3,X4) & r1_orders_2(sK2,X5,X6) & X4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK1,sK3,X4) & r1_orders_2(sK2,X5,X6) & X4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : (? [X6] : (~r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK2,X5,X6) & sK4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X5] : (? [X6] : (~r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK2,X5,X6) & sK4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) => (? [X6] : (~r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK2,sK5,X6) & sK4 = X6 & sK3 = sK5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK2)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ? [X6] : (~r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK2,sK5,X6) & sK4 = X6 & sK3 = sK5 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK2,sK5,sK6) & sK4 = sK6 & sK3 = sK5 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X1,X3,X4) & (r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.54    inference(resolution,[],[f127,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.22/0.54    inference(forward_demodulation,[],[f47,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    sK4 = sK6),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.54    inference(resolution,[],[f126,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    r1_orders_2(sK2,sK3,sK4)),
% 0.22/0.54    inference(backward_demodulation,[],[f68,f48])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    r1_orders_2(sK2,sK5,sK4)),
% 0.22/0.54    inference(backward_demodulation,[],[f50,f49])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    r1_orders_2(sK2,sK5,sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_orders_2(sK2,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 0.22/0.54    inference(resolution,[],[f125,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    l1_orders_2(sK2)),
% 0.22/0.54    inference(resolution,[],[f78,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_waybel_0(X0,sK0) | l1_orders_2(X0)) )),
% 0.22/0.54    inference(resolution,[],[f52,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    l1_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | l1_orders_2(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    l1_waybel_0(sK2,sK0)),
% 0.22/0.54    inference(resolution,[],[f76,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    m1_yellow_6(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_yellow_6(X0,sK0,sK1) | l1_waybel_0(X0,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f75,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    l1_waybel_0(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_waybel_0(X1,sK0) | ~m1_yellow_6(X0,sK0,X1) | l1_waybel_0(X0,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f63,f41])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | l1_waybel_0(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~l1_orders_2(sK2) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X1,X2)) )),
% 0.22/0.54    inference(resolution,[],[f123,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,u1_orders_2(sK2))) )),
% 0.22/0.54    inference(resolution,[],[f122,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(u1_orders_2(sK1)))),
% 0.22/0.54    inference(resolution,[],[f89,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))),
% 0.22/0.54    inference(resolution,[],[f88,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    l1_orders_2(sK1)),
% 0.22/0.54    inference(resolution,[],[f72,f42])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ~l1_orders_2(sK1) | r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))),
% 0.22/0.54    inference(resolution,[],[f86,f80])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~l1_orders_2(sK2) | r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) | ~l1_orders_2(sK1)),
% 0.22/0.54    inference(resolution,[],[f84,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.22/0.54  % (23525)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    m1_yellow_0(sK2,sK1)),
% 0.22/0.54    inference(resolution,[],[f83,f42])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ~l1_waybel_0(sK1,sK0) | m1_yellow_0(sK2,sK1)),
% 0.22/0.54    inference(resolution,[],[f82,f78])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ~l1_waybel_0(sK2,sK0) | ~l1_waybel_0(sK1,sK0) | m1_yellow_0(sK2,sK1)),
% 0.22/0.54    inference(resolution,[],[f77,f43])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_yellow_6(X0,sK0,X1) | ~l1_waybel_0(X0,sK0) | ~l1_waybel_0(X1,sK0) | m1_yellow_0(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f53,f41])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | m1_yellow_0(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1)) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | (u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1))) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_orders_2(sK1))) | ~r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f121,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    v1_xboole_0(u1_orders_2(sK1))),
% 0.22/0.54    inference(resolution,[],[f120,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ~r1_orders_2(sK1,sK3,sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    r1_orders_2(sK1,sK3,sK4) | v1_xboole_0(u1_orders_2(sK1))),
% 0.22/0.54    inference(resolution,[],[f119,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_orders_2(sK1)) | r1_orders_2(sK1,sK3,sK4)),
% 0.22/0.54    inference(resolution,[],[f118,f71])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_orders_2(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | r1_orders_2(sK1,sK3,sK4)),
% 0.22/0.54    inference(resolution,[],[f117,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_orders_2(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | r1_orders_2(sK1,sK3,sK4)),
% 0.22/0.54    inference(resolution,[],[f116,f70])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,u1_struct_0(sK2)) | r1_orders_2(sK1,sK3,sK4) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_orders_2(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.22/0.54    inference(resolution,[],[f115,f69])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_orders_2(sK2,X0,X1) | v1_xboole_0(u1_orders_2(sK1)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f114,f73])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_orders_2(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_orders_2(sK1)) | r1_orders_2(sK1,X0,X1) | ~r1_orders_2(sK2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f113,f80])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_orders_2(sK2) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | v1_xboole_0(u1_orders_2(sK1)) | r1_orders_2(sK1,X1,X0) | ~r1_orders_2(sK2,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f98,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X2,X1] : (m1_subset_1(k4_tarski(X1,X2),u1_orders_2(sK1)) | ~r1_orders_2(sK2,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) )),
% 0.22/0.54    inference(resolution,[],[f92,f60])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,u1_orders_2(sK2)) | m1_subset_1(X0,u1_orders_2(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f91,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(k4_tarski(X4,X5),u1_orders_2(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | v1_xboole_0(u1_orders_2(X3)) | r1_orders_2(X3,X4,X5)) )),
% 0.22/0.54    inference(resolution,[],[f61,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (23526)------------------------------
% 0.22/0.54  % (23526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23526)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (23526)Memory used [KB]: 1663
% 0.22/0.54  % (23526)Time elapsed: 0.090 s
% 0.22/0.54  % (23526)------------------------------
% 0.22/0.54  % (23526)------------------------------
% 0.22/0.54  % (23515)Success in time 0.182 s
%------------------------------------------------------------------------------
