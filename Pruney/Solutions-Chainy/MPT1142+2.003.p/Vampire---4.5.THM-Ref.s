%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 634 expanded)
%              Number of leaves         :    8 ( 267 expanded)
%              Depth                    :   21
%              Number of atoms          :  337 (6732 expanded)
%              Number of equality atoms :   12 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(subsumption_resolution,[],[f377,f388])).

fof(f388,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f358,f180])).

fof(f180,plain,(
    ~ r2_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f179,f21])).

fof(f21,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    & ( ( r2_orders_2(sK0,sK2,sK3)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( r1_orders_2(sK0,sK2,sK3)
        & r2_orders_2(sK0,sK1,sK2) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK0,X1,X3)
                  & ( ( r2_orders_2(sK0,X2,X3)
                      & r1_orders_2(sK0,X1,X2) )
                    | ( r1_orders_2(sK0,X2,X3)
                      & r2_orders_2(sK0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(sK0,X1,X3)
                & ( ( r2_orders_2(sK0,X2,X3)
                    & r1_orders_2(sK0,X1,X2) )
                  | ( r1_orders_2(sK0,X2,X3)
                    & r2_orders_2(sK0,X1,X2) ) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(sK0,sK1,X3)
              & ( ( r2_orders_2(sK0,X2,X3)
                  & r1_orders_2(sK0,sK1,X2) )
                | ( r1_orders_2(sK0,X2,X3)
                  & r2_orders_2(sK0,sK1,X2) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_orders_2(sK0,sK1,X3)
            & ( ( r2_orders_2(sK0,X2,X3)
                & r1_orders_2(sK0,sK1,X2) )
              | ( r1_orders_2(sK0,X2,X3)
                & r2_orders_2(sK0,sK1,X2) ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r2_orders_2(sK0,sK1,X3)
          & ( ( r2_orders_2(sK0,sK2,X3)
              & r1_orders_2(sK0,sK1,sK2) )
            | ( r1_orders_2(sK0,sK2,X3)
              & r2_orders_2(sK0,sK1,sK2) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r2_orders_2(sK0,sK1,X3)
        & ( ( r2_orders_2(sK0,sK2,X3)
            & r1_orders_2(sK0,sK1,sK2) )
          | ( r1_orders_2(sK0,sK2,X3)
            & r2_orders_2(sK0,sK1,sK2) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_orders_2(sK0,sK1,sK3)
      & ( ( r2_orders_2(sK0,sK2,sK3)
          & r1_orders_2(sK0,sK1,sK2) )
        | ( r1_orders_2(sK0,sK2,sK3)
          & r2_orders_2(sK0,sK1,sK2) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(f179,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f178,f22])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f178,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f177,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f177,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f167,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f167,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f135,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

fof(f135,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f134,f22])).

fof(f134,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f133,f23])).

fof(f133,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f128,f24])).

fof(f128,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f26,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f358,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f28,f350])).

fof(f350,plain,(
    sK1 = sK3 ),
    inference(resolution,[],[f336,f125])).

fof(f125,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f124,f22])).

% (5057)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f124,plain,
    ( sK1 = sK3
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f123,f23])).

fof(f123,plain,
    ( sK1 = sK3
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f122,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,
    ( sK1 = sK3
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f336,plain,(
    r1_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f335,f160])).

fof(f160,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f159,f22])).

fof(f159,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f158,f24])).

fof(f158,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f153,f25])).

fof(f153,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f29,f31])).

fof(f29,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f335,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK1,sK3) ),
    inference(resolution,[],[f172,f25])).

fof(f172,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f171,f20])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f22])).

fof(f170,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f23])).

fof(f169,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f24])).

fof(f165,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f135,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f28,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f377,plain,(
    ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f199,f350])).

fof(f199,plain,(
    ~ r2_orders_2(sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f198,f21])).

fof(f198,plain,
    ( ~ r2_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f197,f22])).

fof(f197,plain,
    ( ~ r2_orders_2(sK0,sK3,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f196,f24])).

fof(f196,plain,
    ( ~ r2_orders_2(sK0,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f186,f25])).

fof(f186,plain,
    ( ~ r2_orders_2(sK0,sK3,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f160,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:22:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (5059)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (5058)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (5067)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (5059)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (5056)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f377,f388])).
% 0.21/0.48  fof(f388,plain,(
% 0.21/0.48    r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f358,f180])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK2,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f179,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v5_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    (((~r2_orders_2(sK0,sK1,sK3) & ((r2_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,sK3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(sK0,X1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,X1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(sK0,X1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,X1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,sK1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,sK1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,X3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,X3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r2_orders_2(sK0,sK1,sK3) & ((r2_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,sK3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK2,sK1) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f178,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    l1_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK2,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f177,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f167,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK2,sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(resolution,[],[f135,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f22])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f23])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f24])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f127])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(resolution,[],[f26,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    r2_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f28,f350])).
% 0.21/0.48  fof(f350,plain,(
% 0.21/0.48    sK1 = sK3),
% 0.21/0.48    inference(resolution,[],[f336,f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~r1_orders_2(sK0,sK1,sK3) | sK1 = sK3),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f22])).
% 0.21/0.48  % (5057)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    sK1 = sK3 | ~r1_orders_2(sK0,sK1,sK3) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f23])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    sK1 = sK3 | ~r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f122,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    sK1 = sK3 | ~r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(resolution,[],[f30,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK1,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK1,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f335,f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK2,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f159,f22])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f24])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK2,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f25])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f152])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    r1_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.48    inference(resolution,[],[f29,f31])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    r2_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    ~r1_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK1,sK3)),
% 0.21/0.48    inference(resolution,[],[f172,f25])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f171,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v4_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ( ! [X0] : (r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f22])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X0] : (r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v4_orders_2(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f23])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ( ! [X0] : (r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v4_orders_2(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f24])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ( ! [X0] : (r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v4_orders_2(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f135,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_orders_2(X0,X1,X3) | (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    r2_orders_2(sK0,sK2,sK3) | r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f377,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f199,f350])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK3,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f198,f21])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK3,sK2) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f197,f22])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK3,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f196,f24])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK3,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f25])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~r2_orders_2(sK0,sK3,sK2) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.48    inference(resolution,[],[f160,f34])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5059)------------------------------
% 0.21/0.48  % (5059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5059)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5059)Memory used [KB]: 1791
% 0.21/0.48  % (5059)Time elapsed: 0.057 s
% 0.21/0.48  % (5059)------------------------------
% 0.21/0.48  % (5059)------------------------------
% 0.21/0.48  % (5052)Success in time 0.123 s
%------------------------------------------------------------------------------
