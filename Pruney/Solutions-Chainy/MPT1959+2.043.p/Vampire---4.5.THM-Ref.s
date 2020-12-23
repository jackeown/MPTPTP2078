%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 (5407 expanded)
%              Number of leaves         :   12 (1087 expanded)
%              Depth                    :   40
%              Number of atoms          :  467 (32270 expanded)
%              Number of equality atoms :   70 (2280 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2383)Termination reason: Refutation not found, incomplete strategy

% (2383)Memory used [KB]: 10746
% (2383)Time elapsed: 0.131 s
% (2383)------------------------------
% (2383)------------------------------
fof(f341,plain,(
    $false ),
    inference(subsumption_resolution,[],[f338,f330])).

fof(f330,plain,(
    m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f290,f42])).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f290,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f43,f259])).

fof(f259,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f243])).

fof(f243,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f241,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f241,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,
    ( sK1 = u1_struct_0(sK0)
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f229,f210])).

fof(f210,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f206,f69])).

fof(f206,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( sK1 = u1_struct_0(sK0)
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f200,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0)
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f134,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,k1_zfmisc_1(sK1))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0)
      | sK1 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f125,f69])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK1))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0) ) ),
    inference(subsumption_resolution,[],[f123,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1)
      | sK1 = X0
      | ~ r2_hidden(X1,k1_zfmisc_1(sK1))
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f106,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1)
      | sK1 = X0
      | ~ r2_hidden(X1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f105,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1)
      | sK1 = X0
      | ~ r2_hidden(X1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1)
      | sK1 = X0
      | ~ r2_hidden(X1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1)
      | sK1 = X0
      | ~ r2_hidden(X1,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f90,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f90,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,sK1)
      | sK1 = X3
      | ~ r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X3),X4)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X3),X3) ) ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)
      | sK1 = X0
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f80,f51])).

fof(f80,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),sK1)
      | sK1 = X1 ) ),
    inference(resolution,[],[f36,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0)
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK1))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
      | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f102,f36])).

fof(f102,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X8),X9)
      | sK1 = X8
      | ~ r2_hidden(X9,k1_zfmisc_1(sK1))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X8),X10)
      | ~ r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0)
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(X0,k1_zfmisc_1(sK1))
      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f133,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X1)
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f200,plain,(
    ! [X0] :
      ( r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)
      | sK1 = X0
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f199,f51])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f198,f36])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f187,f56])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | sK1 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f180,f82])).

fof(f82,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f180,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f166,f32])).

fof(f32,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | sK1 = X0
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) ) ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0 ) ),
    inference(resolution,[],[f127,f81])).

fof(f81,plain,(
    ! [X2] :
      ( m1_subset_1(sK4(u1_struct_0(sK0),sK1,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X2 ) ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( sK1 = X0
      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)
      | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f94,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f73,f42])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f72,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f71,f40])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f41,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ r1_orders_2(sK0,X2,sK4(u1_struct_0(sK0),sK1,X1))
      | sK1 = X1
      | ~ r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f93,f35])).

fof(f35,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1)
      | sK1 = X1
      | ~ r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | ~ r1_orders_2(sK0,X2,sK4(u1_struct_0(sK0),sK1,X1))
      | ~ v13_waybel_0(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f89,f36])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1)
      | sK1 = X1
      | ~ r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | ~ r1_orders_2(sK0,X2,sK4(u1_struct_0(sK0),sK1,X1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(sK1,sK0) ) ),
    inference(resolution,[],[f85,f78])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X5,X3)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X4,X3)
      | ~ r1_orders_2(sK0,X4,X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f77,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f77,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X4,X3)
      | ~ r1_orders_2(sK0,X4,X5)
      | r2_hidden(X5,X3)
      | ~ v13_waybel_0(X3,sK0) ) ),
    inference(resolution,[],[f42,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f229,plain,
    ( r1_tarski(sK1,sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f228,f60])).

fof(f228,plain,
    ( ~ r2_hidden(sK5(sK1,sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f216])).

fof(f216,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f215,f69])).

fof(f215,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(sK5(sK1,sK1),sK1) ),
    inference(resolution,[],[f210,f61])).

fof(f224,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(sK5(sK1,sK1),sK1)
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f221,f60])).

fof(f221,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(sK5(sK1,sK1),sK1) ),
    inference(resolution,[],[f216,f61])).

fof(f255,plain,
    ( sK1 = u1_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f248,f60])).

fof(f248,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f243,f61])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f338,plain,(
    ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f337,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f33,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f337,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f336,f262])).

fof(f262,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f36,f259])).

fof(f336,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f260,f67])).

fof(f67,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f260,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f31,f259])).

fof(f31,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (2360)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (2380)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (2372)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (2362)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (2379)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (2358)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (2357)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (2370)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (2368)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (2378)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (2364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (2359)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (2363)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (2365)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (2376)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (2374)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (2384)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (2378)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (2374)Refutation not found, incomplete strategy% (2374)------------------------------
% 0.20/0.52  % (2374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2374)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2374)Memory used [KB]: 10746
% 0.20/0.52  % (2374)Time elapsed: 0.120 s
% 0.20/0.52  % (2374)------------------------------
% 0.20/0.52  % (2374)------------------------------
% 0.20/0.52  % (2369)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (2366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (2385)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (2382)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (2371)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (2361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (2367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (2381)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (2383)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (2386)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (2375)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (2383)Refutation not found, incomplete strategy% (2383)------------------------------
% 0.20/0.54  % (2383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2373)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (2377)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  % (2383)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2383)Memory used [KB]: 10746
% 0.20/0.55  % (2383)Time elapsed: 0.131 s
% 0.20/0.55  % (2383)------------------------------
% 0.20/0.55  % (2383)------------------------------
% 0.20/0.55  fof(f341,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f338,f330])).
% 0.20/0.55  fof(f330,plain,(
% 0.20/0.55    m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f290,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    l1_orders_2(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f12])).
% 0.20/0.55  fof(f12,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.55  fof(f290,plain,(
% 0.20/0.55    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0)),
% 0.20/0.55    inference(superposition,[],[f43,f259])).
% 0.20/0.55  fof(f259,plain,(
% 0.20/0.55    sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f255,f243])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f241,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f236])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    sK1 = u1_struct_0(sK0) | sK1 = u1_struct_0(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(resolution,[],[f229,f210])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    ~r1_tarski(sK1,sK1) | sK1 = u1_struct_0(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(resolution,[],[f206,f69])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f205])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    sK1 = u1_struct_0(sK0) | sK1 = u1_struct_0(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | ~r2_hidden(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.55    inference(resolution,[],[f200,f138])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0) | sK1 = u1_struct_0(sK0) | ~r2_hidden(X0,k1_zfmisc_1(sK1))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f134,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0) | sK1 = u1_struct_0(sK0)) )),
% 0.20/0.55    inference(resolution,[],[f125,f69])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | ~r2_hidden(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f123,f107])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1) | sK1 = X0 | ~r2_hidden(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f106,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1) | sK1 = X0 | ~r2_hidden(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f105,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1) | sK1 = X0 | ~r2_hidden(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1) | sK1 = X0 | ~r2_hidden(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) | sK1 = X0) )),
% 0.20/0.55    inference(resolution,[],[f96,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | X1 = X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(flattening,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X1) | sK1 = X0 | ~r2_hidden(X1,k1_zfmisc_1(sK1))) )),
% 0.20/0.55    inference(resolution,[],[f90,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X4,X3] : (~r1_tarski(X4,sK1) | sK1 = X3 | ~r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X3),X4) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X3),X3)) )),
% 0.20/0.55    inference(resolution,[],[f85,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) | sK1 = X0 | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f80,f51])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),sK1) | sK1 = X1) )),
% 0.20/0.55    inference(resolution,[],[f36,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | X1 = X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0) | sK1 = u1_struct_0(sK0) | ~r2_hidden(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f102,f36])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ( ! [X10,X8,X9] : (~m1_subset_1(X10,k1_zfmisc_1(X8)) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X8),X9) | sK1 = X8 | ~r2_hidden(X9,k1_zfmisc_1(sK1)) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X8),X10) | ~r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f96,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X0) | sK1 = u1_struct_0(sK0) | ~r2_hidden(X0,k1_zfmisc_1(sK1)) | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))) )),
% 0.20/0.55    inference(resolution,[],[f133,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    ( ! [X1] : (~r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),X1) | sK1 = u1_struct_0(sK0) | ~r2_hidden(X1,k1_zfmisc_1(sK1))) )),
% 0.20/0.55    inference(resolution,[],[f128,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) | sK1 = X0 | sK1 = u1_struct_0(sK0) | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f199,f51])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f198,f36])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f190])).
% 0.20/0.55  fof(f190,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),sK1) | sK1 = X0) )),
% 0.20/0.55    inference(resolution,[],[f187,f56])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | sK1 = u1_struct_0(sK0)) )),
% 0.20/0.55    inference(resolution,[],[f180,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f36,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) | sK1 = X0) )),
% 0.20/0.55    inference(resolution,[],[f166,f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = X0 | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f165,f51])).
% 0.20/0.55  fof(f165,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f162])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) )),
% 0.20/0.55    inference(resolution,[],[f127,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X2] : (m1_subset_1(sK4(u1_struct_0(sK0),sK1,X2),u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X2) )),
% 0.20/0.55    inference(resolution,[],[f36,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | X1 = X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(sK4(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f126])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    ( ! [X0] : (sK1 = X0 | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X0),X0) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))) )),
% 0.20/0.55    inference(resolution,[],[f94,f83])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f73,f42])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f72,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ~v2_struct_0(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f71,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    v5_orders_2(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) )),
% 0.20/0.55    inference(resolution,[],[f41,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    v1_yellow_0(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X2,X1] : (~r1_orders_2(sK0,X2,sK4(u1_struct_0(sK0),sK1,X1)) | sK1 = X1 | ~r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f93,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    v13_waybel_0(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ( ! [X2,X1] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1) | sK1 = X1 | ~r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r1_orders_2(sK0,X2,sK4(u1_struct_0(sK0),sK1,X1)) | ~v13_waybel_0(sK1,sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f89,f36])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X2,X1] : (~r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),X1) | sK1 = X1 | ~r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,X1),u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r1_orders_2(sK0,X2,sK4(u1_struct_0(sK0),sK1,X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v13_waybel_0(sK1,sK0)) )),
% 0.20/0.55    inference(resolution,[],[f85,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (r2_hidden(X5,X3) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X4,X3) | ~r1_orders_2(sK0,X4,X5) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v13_waybel_0(X3,sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f77,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X4,X3) | ~r1_orders_2(sK0,X4,X5) | r2_hidden(X5,X3) | ~v13_waybel_0(X3,sK0)) )),
% 0.20/0.55    inference(resolution,[],[f42,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    r1_tarski(sK1,sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f228,f60])).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    ~r2_hidden(sK5(sK1,sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f224,f216])).
% 0.20/0.55  fof(f216,plain,(
% 0.20/0.55    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK1,sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f215,f69])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | ~r2_hidden(sK5(sK1,sK1),sK1)),
% 0.20/0.55    inference(resolution,[],[f210,f61])).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    sK1 = u1_struct_0(sK0) | ~r2_hidden(sK5(sK1,sK1),sK1) | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.55    inference(resolution,[],[f221,f60])).
% 0.20/0.55  fof(f221,plain,(
% 0.20/0.55    ~r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~r2_hidden(sK5(sK1,sK1),sK1)),
% 0.20/0.55    inference(resolution,[],[f216,f61])).
% 0.20/0.55  fof(f255,plain,(
% 0.20/0.55    sK1 = u1_struct_0(sK0) | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.55    inference(resolution,[],[f248,f60])).
% 0.20/0.55  fof(f248,plain,(
% 0.20/0.55    ~r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f243,f61])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.55  fof(f338,plain,(
% 0.20/0.55    ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.20/0.55    inference(resolution,[],[f337,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.55    inference(resolution,[],[f33,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ~v1_xboole_0(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f337,plain,(
% 0.20/0.55    ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f336,f262])).
% 0.20/0.55  fof(f262,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.55    inference(backward_demodulation,[],[f36,f259])).
% 0.20/0.55  fof(f336,plain,(
% 0.20/0.55    ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.55    inference(resolution,[],[f260,f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f260,plain,(
% 0.20/0.55    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.55    inference(backward_demodulation,[],[f31,f259])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (2378)------------------------------
% 0.20/0.55  % (2378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2378)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (2378)Memory used [KB]: 1918
% 0.20/0.55  % (2378)Time elapsed: 0.133 s
% 0.20/0.55  % (2378)------------------------------
% 0.20/0.55  % (2378)------------------------------
% 0.20/0.55  % (2356)Success in time 0.192 s
%------------------------------------------------------------------------------
