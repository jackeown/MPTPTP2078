%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:10 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   90 (1309 expanded)
%              Number of leaves         :    7 ( 225 expanded)
%              Depth                    :   41
%              Number of atoms          :  479 (8490 expanded)
%              Number of equality atoms :   60 ( 267 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f243,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f196,f237])).

fof(f237,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f236,f195])).

fof(f195,plain,(
    m1_orders_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f190])).

fof(f190,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f185,f21])).

fof(f21,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_orders_2(X2,X0,X1)
               => r1_tarski(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f185,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f183,f79])).

fof(f79,plain,(
    r2_hidden(sK4(sK2,sK1),sK2) ),
    inference(resolution,[],[f21,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (13052)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f17,plain,(
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

fof(f183,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f182,f20])).

fof(f182,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f181,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f181,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f180,f86])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f85,f20])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f57,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f56,f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f54,f25])).

fof(f25,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f48,f24])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f180,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f179,f22])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f178,f27])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f177,f26])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f176,f25])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f175,f24])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = sK1
      | v2_struct_0(sK0)
      | ~ m1_orders_2(sK2,sK0,sK1) ) ),
    inference(resolution,[],[f171,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | v2_struct_0(X0)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
      | ~ r2_hidden(sK4(X0,sK1),sK2)
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK2)
      | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1)
      | ~ r2_hidden(sK4(X0,sK1),sK2) ) ),
    inference(resolution,[],[f132,f88])).

fof(f88,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f86,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(X0,sK1),u1_struct_0(sK0))
      | ~ r2_hidden(sK4(X0,sK1),sK2)
      | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
      | k1_xboole_0 = sK1
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f131,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f127,f22])).

fof(f127,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f73,f125])).

fof(f125,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f124,f22])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f123,f86])).

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f65,f20])).

fof(f65,plain,(
    ! [X4,X5] :
      ( ~ m1_orders_2(X5,sK0,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X4
      | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f64,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X4
      | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
      | ~ m1_orders_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f63,f26])).

fof(f63,plain,(
    ! [X4,X5] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X4
      | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
      | ~ m1_orders_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f62,f25])).

fof(f62,plain,(
    ! [X4,X5] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X4
      | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
      | ~ m1_orders_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f50,f24])).

fof(f50,plain,(
    ! [X4,X5] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X4
      | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
      | ~ m1_orders_2(X5,sK0,X4) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X9,X11)
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f72,f23])).

fof(f72,plain,(
    ! [X10,X11,X9] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X9,X11)
      | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) ) ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f71,plain,(
    ! [X10,X11,X9] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X9,X11)
      | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) ) ),
    inference(subsumption_resolution,[],[f70,f25])).

fof(f70,plain,(
    ! [X10,X11,X9] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X9,X11)
      | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) ) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f52,plain,(
    ! [X10,X11,X9] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X9,X11)
      | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) ) ),
    inference(resolution,[],[f27,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f20,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f236,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f225,f203])).

fof(f203,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,k1_xboole_0)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f85,f190])).

fof(f225,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f224,f23])).

fof(f224,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f223,f27])).

% (13048)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f223,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f222,f26])).

fof(f222,plain,(
    ! [X1] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f221,f25])).

fof(f221,plain,(
    ! [X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f214,f24])).

fof(f214,plain,(
    ! [X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,k1_xboole_0) ) ),
    inference(resolution,[],[f197,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f37])).

% (13073)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f197,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f22,f190])).

fof(f196,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f21,f190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (13046)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (13058)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (13053)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (13074)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (13061)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (13066)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (13059)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (13056)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (13057)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13051)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (13072)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (13069)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (13047)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13064)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.53  % (13049)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.53  % (13070)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.53  % (13045)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.53  % (13050)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.53  % (13062)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.53  % (13066)Refutation found. Thanks to Tanya!
% 1.35/0.53  % SZS status Theorem for theBenchmark
% 1.35/0.53  % (13060)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.53  % (13062)Refutation not found, incomplete strategy% (13062)------------------------------
% 1.35/0.53  % (13062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (13062)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (13062)Memory used [KB]: 10618
% 1.35/0.53  % (13062)Time elapsed: 0.130 s
% 1.35/0.53  % (13062)------------------------------
% 1.35/0.53  % (13062)------------------------------
% 1.35/0.54  % (13054)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (13054)Refutation not found, incomplete strategy% (13054)------------------------------
% 1.35/0.54  % (13054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (13054)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (13054)Memory used [KB]: 10618
% 1.35/0.54  % (13054)Time elapsed: 0.142 s
% 1.35/0.54  % (13054)------------------------------
% 1.35/0.54  % (13054)------------------------------
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f247,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(subsumption_resolution,[],[f243,f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.54  fof(f243,plain,(
% 1.35/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.35/0.54    inference(backward_demodulation,[],[f196,f237])).
% 1.35/0.54  fof(f237,plain,(
% 1.35/0.54    k1_xboole_0 = sK2),
% 1.35/0.54    inference(resolution,[],[f236,f195])).
% 1.35/0.54  fof(f195,plain,(
% 1.35/0.54    m1_orders_2(sK2,sK0,k1_xboole_0)),
% 1.35/0.54    inference(backward_demodulation,[],[f20,f190])).
% 1.35/0.54  fof(f190,plain,(
% 1.35/0.54    k1_xboole_0 = sK1),
% 1.35/0.54    inference(subsumption_resolution,[],[f185,f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ~r1_tarski(sK2,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f9])).
% 1.35/0.54  fof(f9,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,negated_conjecture,(
% 1.35/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.35/0.54    inference(negated_conjecture,[],[f7])).
% 1.35/0.54  fof(f7,conjecture,(
% 1.35/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 1.35/0.54  fof(f185,plain,(
% 1.35/0.54    k1_xboole_0 = sK1 | r1_tarski(sK2,sK1)),
% 1.35/0.54    inference(resolution,[],[f183,f79])).
% 1.35/0.54  fof(f79,plain,(
% 1.35/0.54    r2_hidden(sK4(sK2,sK1),sK2)),
% 1.35/0.54    inference(resolution,[],[f21,f40])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f17])).
% 1.35/0.54  % (13052)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  fof(f17,plain,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.35/0.54  fof(f183,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f182,f20])).
% 1.35/0.54  fof(f182,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f181,f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ~v2_struct_0(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f181,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f180,f86])).
% 1.35/0.54  fof(f86,plain,(
% 1.35/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.54    inference(resolution,[],[f85,f20])).
% 1.35/0.54  fof(f85,plain,(
% 1.35/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(resolution,[],[f57,f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f56,f23])).
% 1.35/0.54  fof(f56,plain,(
% 1.35/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f55,f26])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    v5_orders_2(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f55,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f54,f25])).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    v4_orders_2(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f54,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f48,f24])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    v3_orders_2(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(resolution,[],[f27,f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,plain,(
% 1.35/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f15])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    l1_orders_2(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f180,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f179,f22])).
% 1.35/0.54  fof(f179,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f178,f27])).
% 1.35/0.54  fof(f178,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f177,f26])).
% 1.35/0.54  fof(f177,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f176,f25])).
% 1.35/0.54  fof(f176,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f175,f24])).
% 1.35/0.54  fof(f175,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f172])).
% 1.35/0.54  fof(f172,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(resolution,[],[f171,f32])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f14])).
% 1.35/0.54  fof(f14,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f13])).
% 1.35/0.54  fof(f13,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 1.35/0.54  fof(f171,plain,(
% 1.35/0.54    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~r2_hidden(sK4(X0,sK1),sK2) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1)) )),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f169])).
% 1.35/0.54  fof(f169,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1) | ~r2_hidden(sK4(X0,sK1),sK2)) )),
% 1.35/0.54    inference(resolution,[],[f132,f88])).
% 1.35/0.54  fof(f88,plain,(
% 1.35/0.54    ( ! [X1] : (m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK2)) )),
% 1.35/0.54    inference(resolution,[],[f86,f42])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.35/0.54    inference(flattening,[],[f18])).
% 1.35/0.54  fof(f18,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.35/0.54    inference(ennf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.35/0.54  fof(f132,plain,(
% 1.35/0.54    ( ! [X0] : (~m1_subset_1(sK4(X0,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK4(X0,sK1),sK2) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | r1_tarski(X0,sK1)) )),
% 1.35/0.54    inference(resolution,[],[f131,f41])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f17])).
% 1.35/0.54  fof(f131,plain,(
% 1.35/0.54    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = sK1) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f127,f22])).
% 1.35/0.54  fof(f127,plain,(
% 1.35/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = sK1) )),
% 1.35/0.54    inference(superposition,[],[f73,f125])).
% 1.35/0.54  fof(f125,plain,(
% 1.35/0.54    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | k1_xboole_0 = sK1),
% 1.35/0.54    inference(subsumption_resolution,[],[f124,f22])).
% 1.35/0.54  fof(f124,plain,(
% 1.35/0.54    k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.54    inference(subsumption_resolution,[],[f123,f86])).
% 1.35/0.54  fof(f123,plain,(
% 1.35/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.54    inference(resolution,[],[f65,f20])).
% 1.35/0.54  fof(f65,plain,(
% 1.35/0.54    ( ! [X4,X5] : (~m1_orders_2(X5,sK0,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f64,f23])).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    ( ! [X4,X5] : (v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f63,f26])).
% 1.35/0.54  fof(f63,plain,(
% 1.35/0.54    ( ! [X4,X5] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f62,f25])).
% 1.35/0.54  fof(f62,plain,(
% 1.35/0.54    ( ! [X4,X5] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f50,f24])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    ( ! [X4,X5] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) )),
% 1.35/0.54    inference(resolution,[],[f27,f34])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f14])).
% 1.35/0.54  fof(f73,plain,(
% 1.35/0.54    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_orders_2(sK0,X11,X10)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~m1_subset_1(X9,u1_struct_0(sK0))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f72,f23])).
% 1.35/0.54  fof(f72,plain,(
% 1.35/0.54    ( ! [X10,X11,X9] : (v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f71,f26])).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    ( ! [X10,X11,X9] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f70,f25])).
% 1.35/0.54  fof(f70,plain,(
% 1.35/0.54    ( ! [X10,X11,X9] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f52,f24])).
% 1.35/0.54  fof(f52,plain,(
% 1.35/0.54    ( ! [X10,X11,X9] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) )),
% 1.35/0.54    inference(resolution,[],[f27,f30])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f12])).
% 1.35/0.54  fof(f12,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f11])).
% 1.35/0.54  fof(f11,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    m1_orders_2(sK2,sK0,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f236,plain,(
% 1.35/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f225,f203])).
% 1.35/0.54  fof(f203,plain,(
% 1.35/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,k1_xboole_0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.35/0.54    inference(backward_demodulation,[],[f85,f190])).
% 1.35/0.54  fof(f225,plain,(
% 1.35/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f224,f23])).
% 1.35/0.54  fof(f224,plain,(
% 1.35/0.54    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f223,f27])).
% 1.35/0.54  % (13048)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  fof(f223,plain,(
% 1.35/0.54    ( ! [X1] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f222,f26])).
% 1.35/0.54  fof(f222,plain,(
% 1.35/0.54    ( ! [X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f221,f25])).
% 1.35/0.54  fof(f221,plain,(
% 1.35/0.54    ( ! [X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f214,f24])).
% 1.35/0.54  fof(f214,plain,(
% 1.35/0.54    ( ! [X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) )),
% 1.35/0.54    inference(resolution,[],[f197,f43])).
% 1.35/0.54  fof(f43,plain,(
% 1.35/0.54    ( ! [X2,X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f37])).
% 1.35/0.54  % (13073)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  fof(f37,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f14])).
% 1.35/0.54  fof(f197,plain,(
% 1.35/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.54    inference(backward_demodulation,[],[f22,f190])).
% 1.35/0.54  fof(f196,plain,(
% 1.35/0.54    ~r1_tarski(sK2,k1_xboole_0)),
% 1.35/0.54    inference(backward_demodulation,[],[f21,f190])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (13066)------------------------------
% 1.35/0.54  % (13066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (13066)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (13066)Memory used [KB]: 1791
% 1.35/0.54  % (13066)Time elapsed: 0.135 s
% 1.35/0.54  % (13066)------------------------------
% 1.35/0.54  % (13066)------------------------------
% 1.48/0.54  % (13044)Success in time 0.191 s
%------------------------------------------------------------------------------
