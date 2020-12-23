%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1587+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 281 expanded)
%              Number of leaves         :    8 ( 121 expanded)
%              Depth                    :   26
%              Number of atoms          :  351 (3146 expanded)
%              Number of equality atoms :   33 ( 322 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(resolution,[],[f63,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
      | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )
    & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                    & r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                    & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (5695)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3))
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_yellow_0(X1,sK0)
        & v4_yellow_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),X2,X3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X2,X3))
                | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X2,X3)) )
              & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),X2,X3)),u1_struct_0(sK1))
              & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),X2,X3))
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_yellow_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),X2,X3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X2,X3))
              | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X2,X3)) )
            & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),X2,X3)),u1_struct_0(sK1))
            & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),X2,X3))
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ? [X3] :
          ( ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,X3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,X3))
            | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,X3)) )
          & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,X3)),u1_struct_0(sK1))
          & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,X3))
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,X3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,X3))
          | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,X3)) )
        & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,X3)),u1_struct_0(sK1))
        & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,X3))
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
        | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )
      & r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
      & r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ( ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                        & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                     => ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                        & r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                      & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                   => ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      & r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_yellow_0)).

fof(f63,plain,(
    v2_struct_0(sK0) ),
    inference(resolution,[],[f62,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f61,f27])).

fof(f27,plain,(
    r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f60,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f59,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f56,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(backward_demodulation,[],[f41,f53])).

fof(f53,plain,(
    k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(resolution,[],[f52,f18])).

fof(f52,plain,
    ( v2_struct_0(sK0)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(resolution,[],[f51,f21])).

fof(f51,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ) ),
    inference(resolution,[],[f49,f31])).

fof(f49,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f48,f24])).

fof(f48,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | v2_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f47,f25])).

fof(f47,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f46,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,
    ( ~ v4_orders_2(sK0)
    | v2_struct_0(sK1)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f44,f20])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f43,f22])).

fof(f22,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,
    ( ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f30,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_yellow_0)).

fof(f41,plain,
    ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,
    ( ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,
    ( r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f38,f32])).

fof(f38,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f37,f19])).

fof(f37,plain,
    ( ~ v4_orders_2(sK0)
    | v2_struct_0(sK1)
    | r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f36,f20])).

fof(f36,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f22])).

fof(f35,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f34,f23])).

fof(f34,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f33,f26])).

fof(f33,plain,
    ( ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | r2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
