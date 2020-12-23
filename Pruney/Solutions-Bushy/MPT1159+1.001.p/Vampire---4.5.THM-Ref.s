%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1159+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 (1364 expanded)
%              Number of leaves         :   10 ( 493 expanded)
%              Depth                    :   25
%              Number of atoms          :  508 (16501 expanded)
%              Number of equality atoms :   28 ( 212 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f700,plain,(
    $false ),
    inference(subsumption_resolution,[],[f699,f416])).

fof(f416,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f370,f157])).

fof(f157,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(subsumption_resolution,[],[f156,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r2_hidden(sK1,sK3)
      | ~ r2_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r2_orders_2(sK0,sK1,sK2) )
      | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ r2_orders_2(sK0,X1,X2)
                    | ~ r2_hidden(X1,k3_orders_2(sK0,X3,X2)) )
                  & ( ( r2_hidden(X1,X3)
                      & r2_orders_2(sK0,X1,X2) )
                    | r2_hidden(X1,k3_orders_2(sK0,X3,X2)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_hidden(X1,X3)
                  | ~ r2_orders_2(sK0,X1,X2)
                  | ~ r2_hidden(X1,k3_orders_2(sK0,X3,X2)) )
                & ( ( r2_hidden(X1,X3)
                    & r2_orders_2(sK0,X1,X2) )
                  | r2_hidden(X1,k3_orders_2(sK0,X3,X2)) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_hidden(sK1,X3)
                | ~ r2_orders_2(sK0,sK1,X2)
                | ~ r2_hidden(sK1,k3_orders_2(sK0,X3,X2)) )
              & ( ( r2_hidden(sK1,X3)
                  & r2_orders_2(sK0,sK1,X2) )
                | r2_hidden(sK1,k3_orders_2(sK0,X3,X2)) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r2_hidden(sK1,X3)
              | ~ r2_orders_2(sK0,sK1,X2)
              | ~ r2_hidden(sK1,k3_orders_2(sK0,X3,X2)) )
            & ( ( r2_hidden(sK1,X3)
                & r2_orders_2(sK0,sK1,X2) )
              | r2_hidden(sK1,k3_orders_2(sK0,X3,X2)) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ( ~ r2_hidden(sK1,X3)
            | ~ r2_orders_2(sK0,sK1,sK2)
            | ~ r2_hidden(sK1,k3_orders_2(sK0,X3,sK2)) )
          & ( ( r2_hidden(sK1,X3)
              & r2_orders_2(sK0,sK1,sK2) )
            | r2_hidden(sK1,k3_orders_2(sK0,X3,sK2)) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ( ~ r2_hidden(sK1,X3)
          | ~ r2_orders_2(sK0,sK1,sK2)
          | ~ r2_hidden(sK1,k3_orders_2(sK0,X3,sK2)) )
        & ( ( r2_hidden(sK1,X3)
            & r2_orders_2(sK0,sK1,sK2) )
          | r2_hidden(sK1,k3_orders_2(sK0,X3,sK2)) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r2_hidden(sK1,sK3)
        | ~ r2_orders_2(sK0,sK1,sK2)
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) )
      & ( ( r2_hidden(sK1,sK3)
          & r2_orders_2(sK0,sK1,sK2) )
        | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ r2_orders_2(X0,X1,X2)
                    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & ( ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) )
                    | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ r2_orders_2(X0,X1,X2)
                    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & ( ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) )
                    | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <~> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <~> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f156,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f28])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f155,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f154,f29])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f154,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f30])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f153,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f31])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f152,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f151,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f150,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
                & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

fof(f35,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f370,plain,(
    ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f367,f278])).

fof(f278,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK2))
      | r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) ),
    inference(superposition,[],[f50,f243])).

fof(f243,plain,(
    k3_orders_2(sK0,sK3,sK2) = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)),sK3) ),
    inference(resolution,[],[f145,f33])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_orders_2(sK0,sK3,X0) = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3) ) ),
    inference(backward_demodulation,[],[f144,f139])).

fof(f139,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK3) = k3_xboole_0(X1,sK3) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f144,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f143,f27])).

fof(f143,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f28])).

fof(f142,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f29])).

fof(f141,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f30])).

fof(f140,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f31])).

fof(f138,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f367,plain,
    ( ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f330,f221])).

fof(f221,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f102,f33])).

fof(f102,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))
      | r2_orders_2(sK0,sK1,X3) ) ),
    inference(subsumption_resolution,[],[f101,f27])).

fof(f101,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,sK1,X3)
      | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f28])).

fof(f100,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,sK1,X3)
      | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f29])).

fof(f99,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,sK1,X3)
      | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f30])).

fof(f98,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,sK1,X3)
      | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f81,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,sK1,X3)
      | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f330,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(resolution,[],[f279,f37])).

% (2177)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f37,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f279,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,k3_orders_2(sK0,sK3,sK2)) ) ),
    inference(superposition,[],[f49,f243])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f699,plain,(
    ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(subsumption_resolution,[],[f696,f370])).

fof(f696,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f280,f457])).

fof(f457,plain,(
    r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f414,f49])).

fof(f414,plain,(
    r2_hidden(sK1,k3_xboole_0(k3_xboole_0(sK3,sK3),sK3)) ),
    inference(resolution,[],[f370,f183])).

fof(f183,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k3_xboole_0(k3_xboole_0(sK3,sK3),sK3)) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( r2_hidden(sK1,k3_xboole_0(k3_xboole_0(sK3,sK3),sK3))
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(resolution,[],[f147,f166])).

fof(f166,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK3,sK3))
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK3,sK3))
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(resolution,[],[f146,f36])).

fof(f36,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | r2_hidden(sK1,k3_xboole_0(sK3,X0))
      | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

% (2187)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f147,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,X1)
      | r2_hidden(sK1,k3_xboole_0(X1,sK3))
      | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ) ),
    inference(resolution,[],[f36,f48])).

fof(f280,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3)
      | r2_hidden(X2,k3_orders_2(sK0,sK3,sK2))
      | ~ r2_hidden(X2,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) ),
    inference(superposition,[],[f48,f243])).

%------------------------------------------------------------------------------
