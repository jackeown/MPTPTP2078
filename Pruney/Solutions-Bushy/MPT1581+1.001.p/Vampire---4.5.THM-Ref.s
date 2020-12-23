%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1581+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:08 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 454 expanded)
%              Number of leaves         :   14 ( 224 expanded)
%              Depth                    :   15
%              Number of atoms          :  302 (4516 expanded)
%              Number of equality atoms :   36 (1028 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(subsumption_resolution,[],[f240,f107])).

fof(f107,plain,(
    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1)) ),
    inference(subsumption_resolution,[],[f106,f68])).

fof(f68,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    & r1_orders_2(sK1,sK4,sK5)
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f25,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_orders_2(X0,X2,X3)
                            & r1_orders_2(X1,X4,X5)
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(sK0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_orders_2(sK0,X2,X3)
                        & r1_orders_2(X1,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_yellow_0(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_orders_2(sK0,X2,X3)
                      & r1_orders_2(sK1,X4,X5)
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_yellow_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_orders_2(sK0,X2,X3)
                    & r1_orders_2(sK1,X4,X5)
                    & X3 = X5
                    & X2 = X4
                    & m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_orders_2(sK0,sK2,X3)
                  & r1_orders_2(sK1,X4,X5)
                  & X3 = X5
                  & sK2 = X4
                  & m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_orders_2(sK0,sK2,X3)
                & r1_orders_2(sK1,X4,X5)
                & X3 = X5
                & sK2 = X4
                & m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_orders_2(sK0,sK2,sK3)
              & r1_orders_2(sK1,X4,X5)
              & sK3 = X5
              & sK2 = X4
              & m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r1_orders_2(sK0,sK2,sK3)
            & r1_orders_2(sK1,X4,X5)
            & sK3 = X5
            & sK2 = X4
            & m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ~ r1_orders_2(sK0,sK2,sK3)
          & r1_orders_2(sK1,sK4,X5)
          & sK3 = X5
          & sK2 = sK4
          & m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X5] :
        ( ~ r1_orders_2(sK0,sK2,sK3)
        & r1_orders_2(sK1,sK4,X5)
        & sK3 = X5
        & sK2 = sK4
        & m1_subset_1(X5,u1_struct_0(sK1)) )
   => ( ~ r1_orders_2(sK0,sK2,sK3)
      & r1_orders_2(sK1,sK4,sK5)
      & sK3 = sK5
      & sK2 = sK4
      & m1_subset_1(sK5,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f65,plain,
    ( l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f32,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f105,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f35,f37])).

fof(f37,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f104,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f36,f38])).

fof(f38,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f53,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f53,plain,(
    r1_orders_2(sK1,sK2,sK3) ),
    inference(backward_demodulation,[],[f52,f37])).

fof(f52,plain,(
    r1_orders_2(sK1,sK4,sK3) ),
    inference(backward_demodulation,[],[f39,f38])).

fof(f39,plain,(
    r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f240,plain,(
    ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1)) ),
    inference(subsumption_resolution,[],[f238,f166])).

fof(f166,plain,(
    ~ v1_xboole_0(u1_orders_2(sK0)) ),
    inference(resolution,[],[f135,f131])).

fof(f131,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0))) ),
    inference(resolution,[],[f72,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,(
    r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f71,f31])).

fof(f71,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f67,f68])).

fof(f67,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f107,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f238,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1)) ),
    inference(resolution,[],[f133,f157])).

fof(f157,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_orders_2(sK0))
      | ~ r2_hidden(X1,u1_orders_2(sK1)) ) ),
    inference(resolution,[],[f131,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f133,plain,
    ( ~ m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | v1_xboole_0(u1_orders_2(sK0)) ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f103,plain,(
    ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f102,f31])).

fof(f102,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f101,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f100,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

% (11821)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f100,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ~ r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
