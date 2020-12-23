%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  159 (2200 expanded)
%              Number of leaves         :   25 ( 508 expanded)
%              Depth                    :   39
%              Number of atoms          :  673 (18318 expanded)
%              Number of equality atoms :   48 ( 311 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1322,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1321,f1168])).

fof(f1168,plain,(
    m1_subset_1(k3_yellow_0(sK6),sK7) ),
    inference(backward_demodulation,[],[f175,f1140])).

fof(f1140,plain,(
    u1_struct_0(sK6) = sK7 ),
    inference(subsumption_resolution,[],[f1139,f471])).

fof(f471,plain,
    ( m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[],[f269,f126])).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f269,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK6))
      | sK7 = X0
      | m1_subset_1(sK11(u1_struct_0(sK6),sK7,X0),u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f147,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f147,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | m1_subset_1(sK11(u1_struct_0(sK6),sK7,X1),u1_struct_0(sK6))
      | sK7 = X1 ) ),
    inference(resolution,[],[f83,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK11(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( sP5(X2,sK11(X0,X1,X2),X1)
            & m1_subset_1(sK11(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP5(X2,X3,X1)
          & m1_subset_1(X3,X0) )
     => ( sP5(X2,sK11(X0,X1,X2),X1)
        & m1_subset_1(sK11(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( sP5(X2,X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X3,X1] :
      ( ( r2_hidden(X3,X1)
      <~> r2_hidden(X3,X2) )
      | ~ sP5(X2,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f83,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f53])).

% (4961)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f53,plain,
    ( ( r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
    & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | v1_subset_1(sK7,u1_struct_0(sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v13_waybel_0(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l1_orders_2(sK6)
    & v1_yellow_0(sK6)
    & v5_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f50,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK6),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
          & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
            | v1_subset_1(X1,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v13_waybel_0(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK6)
      & v1_yellow_0(sK6)
      & v5_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK6),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
        & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
          | v1_subset_1(X1,u1_struct_0(sK6)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        & v13_waybel_0(X1,sK6)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK6),sK7)
        | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
      & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
        | v1_subset_1(sK7,u1_struct_0(sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
      & v13_waybel_0(sK7,sK6)
      & ~ v1_xboole_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
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
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f1139,plain,
    ( ~ m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | u1_struct_0(sK6) = sK7 ),
    inference(subsumption_resolution,[],[f1138,f189])).

fof(f189,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(subsumption_resolution,[],[f188,f83])).

fof(f188,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[],[f85,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f85,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f1138,plain,
    ( ~ m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(subsumption_resolution,[],[f1135,f159])).

fof(f159,plain,(
    sP0(sK7,sK6) ),
    inference(subsumption_resolution,[],[f157,f82])).

fof(f82,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f157,plain,
    ( sP0(sK7,sK6)
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(resolution,[],[f154,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

% (4959)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f154,plain,(
    sP1(sK6,sK7) ),
    inference(subsumption_resolution,[],[f144,f80])).

fof(f80,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f144,plain,
    ( sP1(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f83,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f26,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1135,plain,
    ( ~ m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ sP0(sK7,sK6)
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[],[f293,f1064])).

fof(f1064,plain,
    ( ~ r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(subsumption_resolution,[],[f1063,f914])).

fof(f914,plain,
    ( r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | u1_struct_0(sK6) = sK7 ),
    inference(subsumption_resolution,[],[f906,f189])).

fof(f906,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[],[f874,f471])).

fof(f874,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK6))
      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | r2_hidden(X11,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f873,f159])).

fof(f873,plain,(
    ! [X11] :
      ( r2_hidden(X11,u1_struct_0(sK6))
      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ m1_subset_1(X11,u1_struct_0(sK6))
      | ~ sP0(sK7,sK6) ) ),
    inference(subsumption_resolution,[],[f861,f175])).

fof(f861,plain,(
    ! [X11] :
      ( r2_hidden(X11,u1_struct_0(sK6))
      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ m1_subset_1(X11,u1_struct_0(sK6))
      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
      | ~ sP0(sK7,sK6) ) ),
    inference(duplicate_literal_removal,[],[f857])).

fof(f857,plain,(
    ! [X11] :
      ( r2_hidden(X11,u1_struct_0(sK6))
      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ m1_subset_1(X11,u1_struct_0(sK6))
      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
      | ~ sP0(sK7,sK6)
      | ~ m1_subset_1(X11,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f209,f245])).

fof(f245,plain,(
    ! [X0] :
      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f243,f137])).

fof(f137,plain,(
    ! [X4] :
      ( r2_lattice3(sK6,k1_xboole_0,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f80,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f243,plain,(
    ! [X0] :
      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0)
      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f241,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X1,X0,X4)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK10(X0,X1,X2))
          & r2_lattice3(X1,X2,sK10(X0,X1,X2))
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK10(X0,X1,X2))
        & r2_lattice3(X1,X2,sK10(X0,X1,X2))
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f241,plain,(
    sP2(k3_yellow_0(sK6),sK6,k1_xboole_0) ),
    inference(resolution,[],[f239,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ~ sP2(X2,X1,X0)
        | ~ r2_lattice3(X1,X0,X2) )
      & ( ( sP2(X2,X1,X0)
          & r2_lattice3(X1,X0,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( sP2(X2,X0,X1)
          & r2_lattice3(X0,X1,X2) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( sP2(X2,X0,X1)
          & r2_lattice3(X0,X1,X2) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ( sP2(X2,X0,X1)
        & r2_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f239,plain,(
    sP3(k1_xboole_0,sK6,k3_yellow_0(sK6)) ),
    inference(forward_demodulation,[],[f238,f138])).

fof(f138,plain,(
    k3_yellow_0(sK6) = k1_yellow_0(sK6,k1_xboole_0) ),
    inference(resolution,[],[f80,f86])).

fof(f86,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f238,plain,(
    sP3(k1_xboole_0,sK6,k1_yellow_0(sK6,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f236,f133])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(resolution,[],[f80,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f236,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6))
    | sP3(k1_xboole_0,sK6,k1_yellow_0(sK6,k1_xboole_0)) ),
    inference(resolution,[],[f156,f123])).

fof(f123,plain,(
    ! [X2,X1] :
      ( sP3(X2,X1,k1_yellow_0(X1,X2))
      | ~ sP4(k1_yellow_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k1_yellow_0(X1,X2) != X0
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_yellow_0(X1,X2) = X0
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | k1_yellow_0(X1,X2) != X0 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ( ( k1_yellow_0(X0,X1) = X2
          | ~ sP3(X1,X0,X2) )
        & ( sP3(X1,X0,X2)
          | k1_yellow_0(X0,X1) != X2 ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( k1_yellow_0(X0,X1) = X2
      <=> sP3(X1,X0,X2) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f156,plain,(
    ! [X0] :
      ( sP4(X0,sK6,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f155,f80])).

fof(f155,plain,(
    ! [X0] :
      ( sP4(X0,sK6,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(resolution,[],[f141,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X2,X0,X1)
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f28,f45,f44,f43])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f141,plain,(
    r1_yellow_0(sK6,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f140,f77])).

fof(f77,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f140,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f139,f78])).

fof(f78,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | ~ v5_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f134,f79])).

fof(f79,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f134,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | ~ v1_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f80,f107])).

fof(f107,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f209,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_orders_2(X9,X10,X8)
      | r2_hidden(X8,u1_struct_0(sK6))
      | ~ r2_hidden(X10,sK7)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ sP0(sK7,X9) ) ),
    inference(resolution,[],[f146,f90])).

fof(f90,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X0)
          & r1_orders_2(X1,sK8(X0,X1),sK9(X0,X1))
          & r2_hidden(sK8(X0,X1),X0)
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK8(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r1_orders_2(X1,X2,X3)
              & r2_hidden(X2,X0)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r1_orders_2(X1,sK8(X0,X1),X3)
            & r2_hidden(sK8(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_orders_2(X1,sK8(X0,X1),X3)
          & r2_hidden(sK8(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK9(X0,X1),X0)
        & r1_orders_2(X1,sK8(X0,X1),sK9(X0,X1))
        & r2_hidden(sK8(X0,X1),X0)
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r1_orders_2(X1,X2,X3)
                & r2_hidden(X2,X0)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r1_orders_2(X0,X2,X3)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | r2_hidden(X0,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f83,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1063,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7) ),
    inference(resolution,[],[f504,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X1,X0)
          | ~ r2_hidden(X1,X2) )
        & ( r2_hidden(X1,X0)
          | r2_hidden(X1,X2) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X2,X3,X1] :
      ( ( ( ~ r2_hidden(X3,X2)
          | ~ r2_hidden(X3,X1) )
        & ( r2_hidden(X3,X2)
          | r2_hidden(X3,X1) ) )
      | ~ sP5(X2,X3,X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f504,plain,
    ( sP5(u1_struct_0(sK6),sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[],[f297,f126])).

fof(f297,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK6))
      | sK7 = X0
      | sP5(X0,sK11(u1_struct_0(sK6),sK7,X0),sK7) ) ),
    inference(resolution,[],[f149,f121])).

fof(f149,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP5(X3,sK11(u1_struct_0(sK6),sK7,X3),sK7)
      | sK7 = X3 ) ),
    inference(resolution,[],[f83,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | sP5(X2,sK11(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f293,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ r2_hidden(k3_yellow_0(sK6),X1)
      | ~ sP0(X1,sK6) ) ),
    inference(subsumption_resolution,[],[f292,f175])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(k3_yellow_0(sK6),X1)
      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
      | ~ sP0(X1,sK6) ) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(k3_yellow_0(sK6),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
      | ~ sP0(X1,sK6) ) ),
    inference(resolution,[],[f245,f90])).

fof(f175,plain,(
    m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f171,f80])).

fof(f171,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(superposition,[],[f133,f86])).

fof(f1321,plain,(
    ~ m1_subset_1(k3_yellow_0(sK6),sK7) ),
    inference(subsumption_resolution,[],[f1317,f81])).

fof(f81,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f1317,plain,
    ( v1_xboole_0(sK7)
    | ~ m1_subset_1(k3_yellow_0(sK6),sK7) ),
    inference(resolution,[],[f1315,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1315,plain,(
    ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(subsumption_resolution,[],[f1148,f1300])).

fof(f1300,plain,(
    ~ v1_subset_1(sK7,sK7) ),
    inference(resolution,[],[f1147,f124])).

fof(f124,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1147,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK7)) ),
    inference(backward_demodulation,[],[f83,f1140])).

fof(f1148,plain,
    ( v1_subset_1(sK7,sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(backward_demodulation,[],[f84,f1140])).

fof(f84,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (4958)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.46  % (4958)Refutation not found, incomplete strategy% (4958)------------------------------
% 0.20/0.46  % (4958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4965)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.48  % (4958)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (4958)Memory used [KB]: 10746
% 0.20/0.48  % (4958)Time elapsed: 0.057 s
% 0.20/0.48  % (4958)------------------------------
% 0.20/0.48  % (4958)------------------------------
% 0.20/0.48  % (4964)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.48  % (4964)Refutation not found, incomplete strategy% (4964)------------------------------
% 0.20/0.48  % (4964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4964)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (4964)Memory used [KB]: 1663
% 0.20/0.48  % (4964)Time elapsed: 0.072 s
% 0.20/0.48  % (4964)------------------------------
% 0.20/0.48  % (4964)------------------------------
% 0.20/0.49  % (4957)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (4957)Refutation not found, incomplete strategy% (4957)------------------------------
% 0.20/0.49  % (4957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4957)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4957)Memory used [KB]: 10618
% 0.20/0.49  % (4957)Time elapsed: 0.081 s
% 0.20/0.49  % (4957)------------------------------
% 0.20/0.49  % (4957)------------------------------
% 0.20/0.51  % (4965)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f1322,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f1321,f1168])).
% 0.20/0.51  fof(f1168,plain,(
% 0.20/0.51    m1_subset_1(k3_yellow_0(sK6),sK7)),
% 0.20/0.51    inference(backward_demodulation,[],[f175,f1140])).
% 0.20/0.51  fof(f1140,plain,(
% 0.20/0.51    u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(subsumption_resolution,[],[f1139,f471])).
% 0.20/0.51  fof(f471,plain,(
% 0.20/0.51    m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(resolution,[],[f269,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f269,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK6)) | sK7 = X0 | m1_subset_1(sK11(u1_struct_0(sK6),sK7,X0),u1_struct_0(sK6))) )),
% 0.20/0.51    inference(resolution,[],[f147,f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | m1_subset_1(sK11(u1_struct_0(sK6),sK7,X1),u1_struct_0(sK6)) | sK7 = X1) )),
% 0.20/0.51    inference(resolution,[],[f83,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK11(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (X1 = X2 | (sP5(X2,sK11(X0,X1,X2),X1) & m1_subset_1(sK11(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (sP5(X2,X3,X1) & m1_subset_1(X3,X0)) => (sP5(X2,sK11(X0,X1,X2),X1) & m1_subset_1(sK11(X0,X1,X2),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (sP5(X2,X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(definition_folding,[],[f37,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X2,X3,X1] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~sP5(X2,X3,X1))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  % (4961)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f50,f52,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.51  fof(f15,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f14])).
% 0.20/0.51  fof(f14,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.51  fof(f1139,plain,(
% 0.20/0.51    ~m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(subsumption_resolution,[],[f1138,f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(subsumption_resolution,[],[f188,f83])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7 | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 0.20/0.51    inference(resolution,[],[f85,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~v1_subset_1(sK7,u1_struct_0(sK6)) | r2_hidden(k3_yellow_0(sK6),sK7)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f1138,plain,(
% 0.20/0.51    ~m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(subsumption_resolution,[],[f1135,f159])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    sP0(sK7,sK6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f157,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    v13_waybel_0(sK7,sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    sP0(sK7,sK6) | ~v13_waybel_0(sK7,sK6)),
% 0.20/0.51    inference(resolution,[],[f154,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sP0(X1,X0) | ~v13_waybel_0(X1,X0) | ~sP1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f41])).
% 0.20/0.51  % (4959)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    sP1(sK6,sK7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f144,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    l1_orders_2(sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    sP1(sK6,sK7) | ~l1_orders_2(sK6)),
% 0.20/0.51    inference(resolution,[],[f83,f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(definition_folding,[],[f26,f41,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.51  fof(f1135,plain,(
% 0.20/0.51    ~m1_subset_1(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),sK7) | ~sP0(sK7,sK6) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(resolution,[],[f293,f1064])).
% 0.20/0.51  fof(f1064,plain,(
% 0.20/0.51    ~r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(subsumption_resolution,[],[f1063,f914])).
% 0.20/0.51  fof(f914,plain,(
% 0.20/0.51    r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(subsumption_resolution,[],[f906,f189])).
% 0.20/0.51  fof(f906,plain,(
% 0.20/0.51    ~r2_hidden(k3_yellow_0(sK6),sK7) | r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(resolution,[],[f874,f471])).
% 0.20/0.51  fof(f874,plain,(
% 0.20/0.51    ( ! [X11] : (~m1_subset_1(X11,u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),sK7) | r2_hidden(X11,u1_struct_0(sK6))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f873,f159])).
% 0.20/0.51  fof(f873,plain,(
% 0.20/0.51    ( ! [X11] : (r2_hidden(X11,u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),sK7) | ~m1_subset_1(X11,u1_struct_0(sK6)) | ~sP0(sK7,sK6)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f861,f175])).
% 0.20/0.51  fof(f861,plain,(
% 0.20/0.51    ( ! [X11] : (r2_hidden(X11,u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),sK7) | ~m1_subset_1(X11,u1_struct_0(sK6)) | ~m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) | ~sP0(sK7,sK6)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f857])).
% 0.20/0.51  fof(f857,plain,(
% 0.20/0.51    ( ! [X11] : (r2_hidden(X11,u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),sK7) | ~m1_subset_1(X11,u1_struct_0(sK6)) | ~m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) | ~sP0(sK7,sK6) | ~m1_subset_1(X11,u1_struct_0(sK6))) )),
% 0.20/0.51    inference(resolution,[],[f209,f245])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ( ! [X0] : (r1_orders_2(sK6,k3_yellow_0(sK6),X0) | ~m1_subset_1(X0,u1_struct_0(sK6))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f243,f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ( ! [X4] : (r2_lattice3(sK6,k1_xboole_0,X4) | ~m1_subset_1(X4,u1_struct_0(sK6))) )),
% 0.20/0.51    inference(resolution,[],[f80,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    ( ! [X0] : (r1_orders_2(sK6,k3_yellow_0(sK6),X0) | ~r2_lattice3(sK6,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK6))) )),
% 0.20/0.51    inference(resolution,[],[f241,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP2(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r1_orders_2(X1,X0,sK10(X0,X1,X2)) & r2_lattice3(X1,X2,sK10(X0,X1,X2)) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f66,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X0,sK10(X0,X1,X2)) & r2_lattice3(X1,X2,sK10(X0,X1,X2)) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.20/0.51    inference(rectify,[],[f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X2,X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.51  fof(f241,plain,(
% 0.20/0.51    sP2(k3_yellow_0(sK6),sK6,k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f239,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | ~r2_lattice3(X1,X0,X2)) & ((sP2(X2,X1,X0) & r2_lattice3(X1,X0,X2)) | ~sP3(X0,X1,X2)))),
% 0.20/0.51    inference(rectify,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ~sP2(X2,X0,X1) | ~r2_lattice3(X0,X1,X2)) & ((sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)) | ~sP3(X1,X0,X2)))),
% 0.20/0.51    inference(flattening,[],[f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | (~sP2(X2,X0,X1) | ~r2_lattice3(X0,X1,X2))) & ((sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)) | ~sP3(X1,X0,X2)))),
% 0.20/0.51    inference(nnf_transformation,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> (sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    sP3(k1_xboole_0,sK6,k3_yellow_0(sK6))),
% 0.20/0.51    inference(forward_demodulation,[],[f238,f138])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    k3_yellow_0(sK6) = k1_yellow_0(sK6,k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f80,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    sP3(k1_xboole_0,sK6,k1_yellow_0(sK6,k1_xboole_0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f236,f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6))) )),
% 0.20/0.51    inference(resolution,[],[f80,f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    ~m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6)) | sP3(k1_xboole_0,sK6,k1_yellow_0(sK6,k1_xboole_0))),
% 0.20/0.51    inference(resolution,[],[f156,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X2,X1] : (sP3(X2,X1,k1_yellow_0(X1,X2)) | ~sP4(k1_yellow_0(X1,X2),X1,X2)) )),
% 0.20/0.51    inference(equality_resolution,[],[f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | k1_yellow_0(X1,X2) != X0 | ~sP4(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((k1_yellow_0(X1,X2) = X0 | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | k1_yellow_0(X1,X2) != X0)) | ~sP4(X0,X1,X2))),
% 0.20/0.51    inference(rectify,[],[f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ! [X2,X0,X1] : (((k1_yellow_0(X0,X1) = X2 | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | k1_yellow_0(X0,X1) != X2)) | ~sP4(X2,X0,X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X2,X0,X1] : ((k1_yellow_0(X0,X1) = X2 <=> sP3(X1,X0,X2)) | ~sP4(X2,X0,X1))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ( ! [X0] : (sP4(X0,sK6,k1_xboole_0) | ~m1_subset_1(X0,u1_struct_0(sK6))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f155,f80])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    ( ! [X0] : (sP4(X0,sK6,k1_xboole_0) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~l1_orders_2(sK6)) )),
% 0.20/0.51    inference(resolution,[],[f141,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (sP4(X2,X0,X1) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(definition_folding,[],[f28,f45,f44,f43])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    r1_yellow_0(sK6,k1_xboole_0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f140,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ~v2_struct_0(sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    r1_yellow_0(sK6,k1_xboole_0) | v2_struct_0(sK6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f139,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    v5_orders_2(sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    r1_yellow_0(sK6,k1_xboole_0) | ~v5_orders_2(sK6) | v2_struct_0(sK6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f134,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    v1_yellow_0(sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    r1_yellow_0(sK6,k1_xboole_0) | ~v1_yellow_0(sK6) | ~v5_orders_2(sK6) | v2_struct_0(sK6)),
% 0.20/0.51    inference(resolution,[],[f80,f107])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    ( ! [X10,X8,X9] : (~r1_orders_2(X9,X10,X8) | r2_hidden(X8,u1_struct_0(sK6)) | ~r2_hidden(X10,sK7) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~sP0(sK7,X9)) )),
% 0.20/0.51    inference(resolution,[],[f146,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK9(X0,X1),X0) & r1_orders_2(X1,sK8(X0,X1),sK9(X0,X1)) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(sK9(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f56,f58,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK8(X0,X1),X3) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1),u1_struct_0(X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK8(X0,X1),X3) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK9(X0,X1),X0) & r1_orders_2(X1,sK8(X0,X1),sK9(X0,X1)) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(sK9(X0,X1),u1_struct_0(X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f40])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK7) | r2_hidden(X0,u1_struct_0(sK6))) )),
% 0.20/0.51    inference(resolution,[],[f83,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f1063,plain,(
% 0.20/0.51    u1_struct_0(sK6) = sK7 | ~r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) | ~r2_hidden(sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)),
% 0.20/0.51    inference(resolution,[],[f504,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X2) | ~sP5(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP5(X0,X1,X2))),
% 0.20/0.51    inference(rectify,[],[f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ! [X2,X3,X1] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~sP5(X2,X3,X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f47])).
% 0.20/0.51  fof(f504,plain,(
% 0.20/0.51    sP5(u1_struct_0(sK6),sK11(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7) | u1_struct_0(sK6) = sK7),
% 0.20/0.51    inference(resolution,[],[f297,f126])).
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK6)) | sK7 = X0 | sP5(X0,sK11(u1_struct_0(sK6),sK7,X0),sK7)) )),
% 0.20/0.51    inference(resolution,[],[f149,f121])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | sP5(X3,sK11(u1_struct_0(sK6),sK7,X3),sK7) | sK7 = X3) )),
% 0.20/0.51    inference(resolution,[],[f83,f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (X1 = X2 | sP5(X2,sK11(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f73])).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),X1) | ~sP0(X1,sK6)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f292,f175])).
% 0.20/0.51  fof(f292,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,X1) | ~r2_hidden(k3_yellow_0(sK6),X1) | ~m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) | ~sP0(X1,sK6)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f290])).
% 0.20/0.51  fof(f290,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,X1) | ~r2_hidden(k3_yellow_0(sK6),X1) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) | ~sP0(X1,sK6)) )),
% 0.20/0.51    inference(resolution,[],[f245,f90])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))),
% 0.20/0.51    inference(subsumption_resolution,[],[f171,f80])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) | ~l1_orders_2(sK6)),
% 0.20/0.51    inference(superposition,[],[f133,f86])).
% 0.20/0.51  fof(f1321,plain,(
% 0.20/0.51    ~m1_subset_1(k3_yellow_0(sK6),sK7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1317,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~v1_xboole_0(sK7)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f1317,plain,(
% 0.20/0.51    v1_xboole_0(sK7) | ~m1_subset_1(k3_yellow_0(sK6),sK7)),
% 0.20/0.51    inference(resolution,[],[f1315,f109])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.51  fof(f1315,plain,(
% 0.20/0.51    ~r2_hidden(k3_yellow_0(sK6),sK7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1148,f1300])).
% 0.20/0.51  fof(f1300,plain,(
% 0.20/0.51    ~v1_subset_1(sK7,sK7)),
% 0.20/0.51    inference(resolution,[],[f1147,f124])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f69])).
% 0.20/0.51  fof(f1147,plain,(
% 0.20/0.51    m1_subset_1(sK7,k1_zfmisc_1(sK7))),
% 0.20/0.51    inference(backward_demodulation,[],[f83,f1140])).
% 0.20/0.51  fof(f1148,plain,(
% 0.20/0.51    v1_subset_1(sK7,sK7) | ~r2_hidden(k3_yellow_0(sK6),sK7)),
% 0.20/0.51    inference(backward_demodulation,[],[f84,f1140])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    v1_subset_1(sK7,u1_struct_0(sK6)) | ~r2_hidden(k3_yellow_0(sK6),sK7)),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (4965)------------------------------
% 0.20/0.51  % (4965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4965)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (4965)Memory used [KB]: 2302
% 0.20/0.51  % (4965)Time elapsed: 0.108 s
% 0.20/0.51  % (4965)------------------------------
% 0.20/0.51  % (4965)------------------------------
% 0.20/0.51  % (4956)Success in time 0.156 s
%------------------------------------------------------------------------------
