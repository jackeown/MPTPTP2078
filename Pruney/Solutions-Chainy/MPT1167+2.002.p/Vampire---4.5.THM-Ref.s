%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 421 expanded)
%              Number of leaves         :    8 (  73 expanded)
%              Depth                    :   30
%              Number of atoms          :  526 (4179 expanded)
%              Number of equality atoms :   56 ( 119 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(subsumption_resolution,[],[f238,f57])).

fof(f57,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f238,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f24,f237])).

fof(f237,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f234,f27])).

fof(f27,plain,(
    ~ r2_hidden(sK1,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( ( m1_orders_2(X4,X0,X3)
                            & r2_hidden(X2,X4)
                            & r2_hidden(X1,X3)
                            & r2_orders_2(X0,X1,X2) )
                         => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

fof(f234,plain,
    ( r2_hidden(sK1,sK4)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f232,f134])).

fof(f134,plain,(
    r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f133,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f133,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(resolution,[],[f132,f24])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,k3_orders_2(sK0,X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f131,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X0)
      | r2_hidden(sK1,k3_orders_2(sK0,X0,sK2)) ) ),
    inference(resolution,[],[f127,f23])).

fof(f23,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f126,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f125,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f124,f34])).

fof(f34,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f123,f33])).

fof(f33,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f122,f32])).

fof(f32,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f232,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK2))
      | r2_hidden(X0,sK4)
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f231,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f231,plain,
    ( r1_tarski(k3_orders_2(sK0,sK3,sK2),sK4)
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( r1_tarski(k3_orders_2(sK0,sK3,sK2),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f227,f153])).

fof(f153,plain,
    ( sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f152,f28])).

fof(f152,plain,
    ( k1_xboole_0 = sK3
    | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f151,f22])).

fof(f22,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f151,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f150,f26])).

fof(f26,plain,(
    m1_orders_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f149,f31])).

fof(f149,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f148,f34])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f147,f33])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f146,f32])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f43,f35])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f227,plain,
    ( r1_tarski(k3_orders_2(sK0,sK3,sK2),k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f223,f89])).

fof(f89,plain,
    ( r2_hidden(sK5(sK0,sK3,sK4),sK3)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f88,f28])).

fof(f88,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK5(sK0,sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f87,f22])).

fof(f87,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | r2_hidden(sK5(sK0,sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f86,f26])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(sK0,X0,X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(sK0,X0,X1),X0)
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(sK0,X0,X1),X0)
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f83,f33])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(sK0,X0,X1),X0)
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK5(sK0,X0,X1),X0)
      | ~ m1_orders_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f223,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(k3_orders_2(sK0,sK3,sK2),k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
    | ~ r2_hidden(sK5(sK0,sK3,sK4),sK3) ),
    inference(resolution,[],[f220,f65])).

fof(f65,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f51,f28])).

fof(f220,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | k1_xboole_0 = sK3
    | r1_tarski(k3_orders_2(sK0,sK3,sK2),k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) ),
    inference(resolution,[],[f199,f28])).

fof(f199,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
      | k1_xboole_0 = sK3
      | r1_tarski(k3_orders_2(sK0,X1,sK2),k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4))) ) ),
    inference(subsumption_resolution,[],[f198,f29])).

fof(f198,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK3
      | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,X1,sK2),k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4))) ) ),
    inference(resolution,[],[f196,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f92,f34])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f91,f33])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f90,f32])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,X1)
      | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1)) ) ),
    inference(resolution,[],[f37,f35])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_orders_2(X0,X1,X2)
      | r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
                 => ( r2_orders_2(X0,X1,X2)
                   => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

fof(f196,plain,
    ( r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f192,f89])).

fof(f192,plain,
    ( r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))
    | k1_xboole_0 = sK3
    | ~ r2_hidden(sK5(sK0,sK3,sK4),sK3) ),
    inference(resolution,[],[f191,f65])).

fof(f191,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f189,f29])).

fof(f189,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f166,f25])).

fof(f25,plain,(
    r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f166,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
      | r2_orders_2(sK0,X4,sK5(sK0,sK3,sK4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f158,f28])).

fof(f158,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X4,sK5(sK0,sK3,sK4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f78,f153])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f74,f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    inference(resolution,[],[f38,f35])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:59:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (7164)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (7156)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (7151)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (7152)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (7159)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (7167)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (7156)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f238,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f50,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.55  fof(f238,plain,(
% 0.22/0.55    r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f24,f237])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    k1_xboole_0 = sK3),
% 0.22/0.55    inference(subsumption_resolution,[],[f234,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ~r2_hidden(sK1,sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_hidden(X1,X4) & (m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f8])).
% 0.22/0.55  fof(f8,conjecture,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    r2_hidden(sK1,sK4) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(resolution,[],[f232,f134])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f133,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))),
% 0.22/0.55    inference(resolution,[],[f132,f24])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k3_orders_2(sK0,X0,sK2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK1,X0) | r2_hidden(sK1,k3_orders_2(sK0,X0,sK2))) )),
% 0.22/0.55    inference(resolution,[],[f127,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,X2) | r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f126,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f125,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ~v2_struct_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f124,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    v5_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f123,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    v4_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f122,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    v3_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(resolution,[],[f40,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    l1_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.22/0.55  fof(f232,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k3_orders_2(sK0,sK3,sK2)) | r2_hidden(X0,sK4) | k1_xboole_0 = sK3) )),
% 0.22/0.55    inference(resolution,[],[f231,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f231,plain,(
% 0.22/0.55    r1_tarski(k3_orders_2(sK0,sK3,sK2),sK4) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f230])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    r1_tarski(k3_orders_2(sK0,sK3,sK2),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3),
% 0.22/0.55    inference(superposition,[],[f227,f153])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(subsumption_resolution,[],[f152,f28])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f151,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(resolution,[],[f150,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    m1_orders_2(sK4,sK0,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_orders_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f31])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f148,f34])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f147,f33])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f146,f32])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | k3_orders_2(sK0,X0,sK5(sK0,X0,X1)) = X1 | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f43,f35])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.22/0.55  fof(f227,plain,(
% 0.22/0.55    r1_tarski(k3_orders_2(sK0,sK3,sK2),k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(subsumption_resolution,[],[f223,f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    r2_hidden(sK5(sK0,sK3,sK4),sK3) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(subsumption_resolution,[],[f88,f28])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | r2_hidden(sK5(sK0,sK3,sK4),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f87,f22])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | r2_hidden(sK5(sK0,sK3,sK4),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(resolution,[],[f86,f26])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_orders_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f85,f31])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f84,f34])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f83,f33])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f82,f32])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f42,f35])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | r1_tarski(k3_orders_2(sK0,sK3,sK2),k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | ~r2_hidden(sK5(sK0,sK3,sK4),sK3)),
% 0.22/0.55    inference(resolution,[],[f220,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X1] : (m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK3)) )),
% 0.22/0.55    inference(resolution,[],[f51,f28])).
% 0.22/0.55  fof(f220,plain,(
% 0.22/0.55    ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | k1_xboole_0 = sK3 | r1_tarski(k3_orders_2(sK0,sK3,sK2),k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))),
% 0.22/0.55    inference(resolution,[],[f199,f28])).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | k1_xboole_0 = sK3 | r1_tarski(k3_orders_2(sK0,X1,sK2),k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4)))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f198,f29])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = sK3 | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,X1,sK2),k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4)))) )),
% 0.22/0.55    inference(resolution,[],[f196,f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f93,f31])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f92,f34])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f91,f33])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f90,f32])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,X1) | r1_tarski(k3_orders_2(sK0,X2,X0),k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(resolution,[],[f37,f35])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_orders_2(X0,X1,X2) | r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_orders_2(X0,X1,X2) => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(subsumption_resolution,[],[f192,f89])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) | k1_xboole_0 = sK3 | ~r2_hidden(sK5(sK0,sK3,sK4),sK3)),
% 0.22/0.55    inference(resolution,[],[f191,f65])).
% 0.22/0.55  fof(f191,plain,(
% 0.22/0.55    ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(subsumption_resolution,[],[f189,f29])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | k1_xboole_0 = sK3),
% 0.22/0.55    inference(resolution,[],[f166,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    r2_hidden(sK2,sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    ( ! [X4] : (~r2_hidden(X4,sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | r2_orders_2(sK0,X4,sK5(sK0,sK3,sK4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k1_xboole_0 = sK3) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f158,f28])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    ( ! [X4] : (~r2_hidden(X4,sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X4,sK5(sK0,sK3,sK4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k1_xboole_0 = sK3) )),
% 0.22/0.55    inference(superposition,[],[f78,f153])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f77,f31])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f76,f34])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f75,f33])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f74,f32])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) )),
% 0.22/0.55    inference(resolution,[],[f38,f35])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    r2_hidden(sK1,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (7156)------------------------------
% 0.22/0.55  % (7156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7156)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (7156)Memory used [KB]: 6396
% 0.22/0.55  % (7156)Time elapsed: 0.115 s
% 0.22/0.55  % (7156)------------------------------
% 0.22/0.55  % (7156)------------------------------
% 0.22/0.55  % (7161)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (7177)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (7153)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (7174)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (7172)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (7165)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (7173)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (7178)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (7168)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (7167)Refutation not found, incomplete strategy% (7167)------------------------------
% 0.22/0.56  % (7167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (7167)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (7167)Memory used [KB]: 10746
% 0.22/0.56  % (7167)Time elapsed: 0.130 s
% 0.22/0.56  % (7167)------------------------------
% 0.22/0.56  % (7167)------------------------------
% 0.22/0.56  % (7150)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (7175)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (7157)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (7162)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (7176)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.57  % (7149)Success in time 0.201 s
%------------------------------------------------------------------------------
