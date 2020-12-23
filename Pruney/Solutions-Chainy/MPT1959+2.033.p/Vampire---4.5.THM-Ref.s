%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 414 expanded)
%              Number of leaves         :   31 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  726 (3043 expanded)
%              Number of equality atoms :   41 (  84 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f129,f159,f336,f342,f496,f502,f552])).

fof(f552,plain,
    ( ~ spl13_1
    | ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f512,f170])).

fof(f170,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f107,f146])).

fof(f146,plain,(
    ! [X0] : sK11(X0) = X0 ),
    inference(subsumption_resolution,[],[f144,f107])).

fof(f144,plain,(
    ! [X0] :
      ( sK11(X0) = X0
      | v1_subset_1(sK11(X0),X0) ) ),
    inference(resolution,[],[f111,f106])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK11(X0),X0)
      & m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f3,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK11(X0),X0)
        & m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f107,plain,(
    ! [X0] : ~ v1_subset_1(sK11(X0),X0) ),
    inference(cnf_transformation,[],[f64])).

fof(f512,plain,
    ( v1_subset_1(sK7,sK7)
    | ~ spl13_1
    | ~ spl13_3 ),
    inference(backward_demodulation,[],[f122,f164])).

fof(f164,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl13_3
  <=> u1_struct_0(sK6) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f122,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl13_1
  <=> v1_subset_1(sK7,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f502,plain,
    ( spl13_3
    | ~ spl13_5
    | spl13_9 ),
    inference(avatar_split_clause,[],[f501,f493,f334,f162])).

fof(f334,plain,
    ( spl13_5
  <=> ! [X0] :
        ( r2_hidden(X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f493,plain,
    ( spl13_9
  <=> r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f501,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ spl13_5
    | spl13_9 ),
    inference(subsumption_resolution,[],[f500,f169])).

fof(f169,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f106,f146])).

fof(f500,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_5
    | spl13_9 ),
    inference(subsumption_resolution,[],[f497,f79])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
    & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | v1_subset_1(sK7,u1_struct_0(sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v13_waybel_0(sK7,sK6)
    & v2_waybel_0(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l1_orders_2(sK6)
    & v1_yellow_0(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f44,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK6),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
          & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
            | v1_subset_1(X1,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v13_waybel_0(X1,sK6)
          & v2_waybel_0(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK6)
      & v1_yellow_0(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK6),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
        & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
          | v1_subset_1(X1,u1_struct_0(sK6)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        & v13_waybel_0(X1,sK6)
        & v2_waybel_0(X1,sK6)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK6),sK7)
        | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
      & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
        | v1_subset_1(sK7,u1_struct_0(sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
      & v13_waybel_0(sK7,sK6)
      & v2_waybel_0(sK7,sK6)
      & ~ v1_xboole_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f497,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl13_5
    | spl13_9 ),
    inference(resolution,[],[f495,f352])).

fof(f352,plain,
    ( ! [X12,X11] :
        ( r2_hidden(sK12(u1_struct_0(sK6),X11,X12),sK7)
        | X11 = X12
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK6))) )
    | ~ spl13_5 ),
    inference(resolution,[],[f335,f115])).

% (6494)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f115,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),X0)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( sP5(X2,sK12(X0,X1,X2),X1)
            & m1_subset_1(sK12(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f42,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP5(X2,X3,X1)
          & m1_subset_1(X3,X0) )
     => ( sP5(X2,sK12(X0,X1,X2),X1)
        & m1_subset_1(sK12(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( sP5(X2,X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X3,X1] :
      ( ( r2_hidden(X3,X1)
      <~> r2_hidden(X3,X2) )
      | ~ sP5(X2,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f335,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7) )
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f334])).

fof(f495,plain,
    ( ~ r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7)
    | spl13_9 ),
    inference(avatar_component_clause,[],[f493])).

fof(f496,plain,
    ( ~ spl13_9
    | spl13_3
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f491,f334,f162,f493])).

fof(f491,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f482,f169])).

fof(f482,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(sK6) = sK7
    | ~ r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7)
    | ~ spl13_5 ),
    inference(resolution,[],[f477,f177])).

fof(f177,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK6))
      | ~ r2_hidden(X0,sK7) ) ),
    inference(resolution,[],[f112,f79])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f477,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK12(u1_struct_0(sK6),X0,sK7),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | sK7 = X0 )
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f476,f79])).

fof(f476,plain,
    ( ! [X0] :
        ( sK7 = X0
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r2_hidden(sK12(u1_struct_0(sK6),X0,sK7),X0) )
    | ~ spl13_5 ),
    inference(duplicate_literal_removal,[],[f474])).

fof(f474,plain,
    ( ! [X0] :
        ( sK7 = X0
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r2_hidden(sK12(u1_struct_0(sK6),X0,sK7),X0)
        | sK7 = X0 )
    | ~ spl13_5 ),
    inference(resolution,[],[f352,f261])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK12(X2,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ r2_hidden(sK12(X2,X0,X1),X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f116,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X1,X0)
          | ~ r2_hidden(X1,X2) )
        & ( r2_hidden(X1,X0)
          | r2_hidden(X1,X2) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X2,X3,X1] :
      ( ( ( ~ r2_hidden(X3,X2)
          | ~ r2_hidden(X3,X1) )
        & ( r2_hidden(X3,X2)
          | r2_hidden(X3,X1) ) )
      | ~ sP5(X2,X3,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,sK12(X0,X1,X2),X1)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f342,plain,(
    spl13_4 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | spl13_4 ),
    inference(subsumption_resolution,[],[f340,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f340,plain,
    ( v2_struct_0(sK6)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f339,f73])).

fof(f73,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f339,plain,
    ( ~ v5_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f338,f74])).

fof(f74,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f338,plain,
    ( ~ v1_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f337,f75])).

fof(f75,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f337,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v1_yellow_0(sK6)
    | ~ v5_orders_2(sK6)
    | v2_struct_0(sK6)
    | spl13_4 ),
    inference(resolution,[],[f332,f104])).

fof(f104,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
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
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f332,plain,
    ( ~ r1_yellow_0(sK6,k1_xboole_0)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl13_4
  <=> r1_yellow_0(sK6,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f336,plain,
    ( ~ spl13_4
    | spl13_5
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f328,f125,f334,f330])).

fof(f125,plain,
    ( spl13_2
  <=> r2_hidden(k3_yellow_0(sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f328,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r1_yellow_0(sK6,k1_xboole_0) )
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f327,f75])).

fof(f327,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r1_yellow_0(sK6,k1_xboole_0)
        | ~ l1_orders_2(sK6) )
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f324,f140])).

fof(f140,plain,(
    sP0(sK7,sK6) ),
    inference(subsumption_resolution,[],[f139,f78])).

fof(f78,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f139,plain,
    ( ~ v13_waybel_0(sK7,sK6)
    | sP0(sK7,sK6) ),
    inference(resolution,[],[f137,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v13_waybel_0(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f137,plain,(
    sP1(sK6,sK7) ),
    inference(subsumption_resolution,[],[f135,f75])).

fof(f135,plain,
    ( sP1(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f93,f79])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f20,f35,f34])).

fof(f34,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f324,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ sP0(sK7,sK6)
        | ~ r1_yellow_0(sK6,k1_xboole_0)
        | ~ l1_orders_2(sK6) )
    | ~ spl13_2 ),
    inference(resolution,[],[f289,f127])).

fof(f127,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f289,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k3_yellow_0(X5),X4)
      | r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ r1_yellow_0(X5,k1_xboole_0)
      | ~ l1_orders_2(X5) ) ),
    inference(subsumption_resolution,[],[f286,f131])).

fof(f131,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f108,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f286,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ r2_hidden(k3_yellow_0(X5),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ r1_yellow_0(X5,k1_xboole_0)
      | ~ l1_orders_2(X5) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ r2_hidden(k3_yellow_0(X5),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ r1_yellow_0(X5,k1_xboole_0)
      | ~ l1_orders_2(X5) ) ),
    inference(resolution,[],[f87,f228])).

fof(f228,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f226,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f99,f216])).

fof(f216,plain,(
    ! [X0] :
      ( sP2(k3_yellow_0(X0),X0,k1_xboole_0)
      | ~ r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f215,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ~ sP2(X2,X1,X0)
        | ~ r2_lattice3(X1,X0,X2) )
      & ( ( sP2(X2,X1,X0)
          & r2_lattice3(X1,X0,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( sP2(X2,X0,X1)
          & r2_lattice3(X0,X1,X2) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r2_lattice3(X0,X1,X2) )
      & ( ( sP2(X2,X0,X1)
          & r2_lattice3(X0,X1,X2) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ( sP2(X2,X0,X1)
        & r2_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f215,plain,(
    ! [X2] :
      ( sP3(k1_xboole_0,X2,k3_yellow_0(X2))
      | ~ l1_orders_2(X2)
      | ~ r1_yellow_0(X2,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f213,f131])).

fof(f213,plain,(
    ! [X2] :
      ( ~ r1_yellow_0(X2,k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0(X2),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | sP3(k1_xboole_0,X2,k3_yellow_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X2] :
      ( ~ r1_yellow_0(X2,k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0(X2),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | sP3(k1_xboole_0,X2,k3_yellow_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f103,f200])).

fof(f200,plain,(
    ! [X0] :
      ( ~ sP4(k3_yellow_0(X0),X0,k1_xboole_0)
      | sP3(k1_xboole_0,X0,k3_yellow_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f118,f82])).

fof(f118,plain,(
    ! [X2,X1] :
      ( ~ sP4(k1_yellow_0(X1,X2),X1,X2)
      | sP3(X2,X1,k1_yellow_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k1_yellow_0(X1,X2) != X0
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_yellow_0(X1,X2) = X0
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | k1_yellow_0(X1,X2) != X0 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ( ( k1_yellow_0(X0,X1) = X2
          | ~ sP3(X1,X0,X2) )
        & ( sP3(X1,X0,X2)
          | k1_yellow_0(X0,X1) != X2 ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ( k1_yellow_0(X0,X1) = X2
      <=> sP3(X1,X0,X2) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X2,X0,X1)
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f22,f39,f38,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK10(X0,X1,X2))
        & r2_lattice3(X1,X2,sK10(X0,X1,X2))
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X1,X4,X5)
      | r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f50,f52,f51])).

fof(f51,plain,(
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

fof(f52,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f159,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl13_1
    | spl13_2 ),
    inference(subsumption_resolution,[],[f157,f75])).

fof(f157,plain,
    ( ~ l1_orders_2(sK6)
    | spl13_1
    | spl13_2 ),
    inference(subsumption_resolution,[],[f153,f134])).

fof(f134,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f132,f76])).

fof(f76,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,
    ( v1_xboole_0(sK7)
    | ~ m1_subset_1(k3_yellow_0(sK6),sK7)
    | spl13_2 ),
    inference(resolution,[],[f109,f126])).

fof(f126,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f153,plain,
    ( m1_subset_1(k3_yellow_0(sK6),sK7)
    | ~ l1_orders_2(sK6)
    | spl13_1 ),
    inference(superposition,[],[f131,f145])).

fof(f145,plain,
    ( u1_struct_0(sK6) = sK7
    | spl13_1 ),
    inference(subsumption_resolution,[],[f143,f123])).

fof(f123,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f143,plain,
    ( u1_struct_0(sK6) = sK7
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(resolution,[],[f111,f79])).

fof(f129,plain,
    ( spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f80,f125,f121])).

fof(f80,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,
    ( ~ spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f81,f125,f121])).

fof(f81,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (6517)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.49  % (6499)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (6492)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (6499)Refutation not found, incomplete strategy% (6499)------------------------------
% 0.21/0.49  % (6499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6499)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6499)Memory used [KB]: 1663
% 0.21/0.49  % (6499)Time elapsed: 0.052 s
% 0.21/0.49  % (6499)------------------------------
% 0.21/0.49  % (6499)------------------------------
% 0.21/0.50  % (6495)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (6496)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (6504)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (6492)Refutation not found, incomplete strategy% (6492)------------------------------
% 0.21/0.51  % (6492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6492)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6492)Memory used [KB]: 10618
% 0.21/0.51  % (6492)Time elapsed: 0.078 s
% 0.21/0.51  % (6492)------------------------------
% 0.21/0.51  % (6492)------------------------------
% 0.21/0.51  % (6505)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (6501)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (6498)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (6502)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (6511)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (6503)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (6500)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (6493)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (6493)Refutation not found, incomplete strategy% (6493)------------------------------
% 0.21/0.52  % (6493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6493)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6493)Memory used [KB]: 10746
% 0.21/0.52  % (6493)Time elapsed: 0.114 s
% 0.21/0.52  % (6493)------------------------------
% 0.21/0.52  % (6493)------------------------------
% 0.21/0.52  % (6509)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (6508)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (6510)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (6496)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f573,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f128,f129,f159,f336,f342,f496,f502,f552])).
% 0.21/0.53  fof(f552,plain,(
% 0.21/0.53    ~spl13_1 | ~spl13_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f551])).
% 0.21/0.53  fof(f551,plain,(
% 0.21/0.53    $false | (~spl13_1 | ~spl13_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f512,f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f107,f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ( ! [X0] : (sK11(X0) = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f107])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X0] : (sK11(X0) = X0 | v1_subset_1(sK11(X0),X0)) )),
% 0.21/0.53    inference(resolution,[],[f111,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK11(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ! [X0] : (~v1_subset_1(sK11(X0),X0) & m1_subset_1(sK11(X0),k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f3,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK11(X0),X0) & m1_subset_1(sK11(X0),k1_zfmisc_1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_subset_1(sK11(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f64])).
% 0.21/0.53  fof(f512,plain,(
% 0.21/0.53    v1_subset_1(sK7,sK7) | (~spl13_1 | ~spl13_3)),
% 0.21/0.53    inference(backward_demodulation,[],[f122,f164])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    u1_struct_0(sK6) = sK7 | ~spl13_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    spl13_3 <=> u1_struct_0(sK6) = sK7),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    v1_subset_1(sK7,u1_struct_0(sK6)) | ~spl13_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl13_1 <=> v1_subset_1(sK7,u1_struct_0(sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.21/0.53  fof(f502,plain,(
% 0.21/0.53    spl13_3 | ~spl13_5 | spl13_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f501,f493,f334,f162])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    spl13_5 <=> ! [X0] : (r2_hidden(X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 0.21/0.53  fof(f493,plain,(
% 0.21/0.53    spl13_9 <=> r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 0.21/0.53  fof(f501,plain,(
% 0.21/0.53    u1_struct_0(sK6) = sK7 | (~spl13_5 | spl13_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f500,f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f106,f146])).
% 0.21/0.53  fof(f500,plain,(
% 0.21/0.53    u1_struct_0(sK6) = sK7 | ~m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) | (~spl13_5 | spl13_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f497,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & v2_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f44,f46,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & v2_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & v2_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & v2_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.21/0.53  fof(f497,plain,(
% 0.21/0.53    u1_struct_0(sK6) = sK7 | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) | (~spl13_5 | spl13_9)),
% 0.21/0.53    inference(resolution,[],[f495,f352])).
% 0.21/0.53  fof(f352,plain,(
% 0.21/0.53    ( ! [X12,X11] : (r2_hidden(sK12(u1_struct_0(sK6),X11,X12),sK7) | X11 = X12 | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK6)))) ) | ~spl13_5),
% 0.21/0.53    inference(resolution,[],[f335,f115])).
% 0.21/0.53  % (6494)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),X0) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (X1 = X2 | (sP5(X2,sK12(X0,X1,X2),X1) & m1_subset_1(sK12(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f42,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (sP5(X2,X3,X1) & m1_subset_1(X3,X0)) => (sP5(X2,sK12(X0,X1,X2),X1) & m1_subset_1(sK12(X0,X1,X2),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (sP5(X2,X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(definition_folding,[],[f31,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X2,X3,X1] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~sP5(X2,X3,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7)) ) | ~spl13_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f334])).
% 0.21/0.53  fof(f495,plain,(
% 0.21/0.53    ~r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7) | spl13_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f493])).
% 0.21/0.53  fof(f496,plain,(
% 0.21/0.53    ~spl13_9 | spl13_3 | ~spl13_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f491,f334,f162,f493])).
% 0.21/0.53  fof(f491,plain,(
% 0.21/0.53    u1_struct_0(sK6) = sK7 | ~r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7) | ~spl13_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f482,f169])).
% 0.21/0.53  fof(f482,plain,(
% 0.21/0.53    ~m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) | u1_struct_0(sK6) = sK7 | ~r2_hidden(sK12(u1_struct_0(sK6),u1_struct_0(sK6),sK7),sK7) | ~spl13_5),
% 0.21/0.53    inference(resolution,[],[f477,f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK6)) | ~r2_hidden(X0,sK7)) )),
% 0.21/0.53    inference(resolution,[],[f112,f79])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK12(u1_struct_0(sK6),X0,sK7),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) | sK7 = X0) ) | ~spl13_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f476,f79])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    ( ! [X0] : (sK7 = X0 | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(sK12(u1_struct_0(sK6),X0,sK7),X0)) ) | ~spl13_5),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f474])).
% 0.21/0.53  fof(f474,plain,(
% 0.21/0.53    ( ! [X0] : (sK7 = X0 | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(sK12(u1_struct_0(sK6),X0,sK7),X0) | sK7 = X0) ) | ~spl13_5),
% 0.21/0.53    inference(resolution,[],[f352,f261])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK12(X2,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~r2_hidden(sK12(X2,X0,X1),X0) | X0 = X1) )),
% 0.21/0.53    inference(resolution,[],[f116,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP5(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ! [X2,X3,X1] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~sP5(X2,X3,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f41])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP5(X2,sK12(X0,X1,X2),X1) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f69])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    spl13_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f341])).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    $false | spl13_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f340,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ~v2_struct_0(sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    v2_struct_0(sK6) | spl13_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f339,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    v5_orders_2(sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    ~v5_orders_2(sK6) | v2_struct_0(sK6) | spl13_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f338,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    v1_yellow_0(sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ~v1_yellow_0(sK6) | ~v5_orders_2(sK6) | v2_struct_0(sK6) | spl13_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f337,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    l1_orders_2(sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    ~l1_orders_2(sK6) | ~v1_yellow_0(sK6) | ~v5_orders_2(sK6) | v2_struct_0(sK6) | spl13_4),
% 0.21/0.53    inference(resolution,[],[f332,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    ~r1_yellow_0(sK6,k1_xboole_0) | spl13_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f330])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    spl13_4 <=> r1_yellow_0(sK6,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    ~spl13_4 | spl13_5 | ~spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f328,f125,f334,f330])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl13_2 <=> r2_hidden(k3_yellow_0(sK6),sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~r1_yellow_0(sK6,k1_xboole_0)) ) | ~spl13_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f327,f75])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~r1_yellow_0(sK6,k1_xboole_0) | ~l1_orders_2(sK6)) ) | ~spl13_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f324,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    sP0(sK7,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f139,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    v13_waybel_0(sK7,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~v13_waybel_0(sK7,sK6) | sP0(sK7,sK6)),
% 0.21/0.53    inference(resolution,[],[f137,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | ~v13_waybel_0(X1,X0) | sP0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    sP1(sK6,sK7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f135,f75])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    sP1(sK6,sK7) | ~l1_orders_2(sK6)),
% 0.21/0.53    inference(resolution,[],[f93,f79])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(definition_folding,[],[f20,f35,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~sP0(sK7,sK6) | ~r1_yellow_0(sK6,k1_xboole_0) | ~l1_orders_2(sK6)) ) | ~spl13_2),
% 0.21/0.53    inference(resolution,[],[f289,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    r2_hidden(k3_yellow_0(sK6),sK7) | ~spl13_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~r2_hidden(k3_yellow_0(X5),X4) | r2_hidden(X3,X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~sP0(X4,X5) | ~r1_yellow_0(X5,k1_xboole_0) | ~l1_orders_2(X5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f286,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(superposition,[],[f108,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (r2_hidden(X3,X4) | ~r2_hidden(k3_yellow_0(X5),X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5)) | ~sP0(X4,X5) | ~r1_yellow_0(X5,k1_xboole_0) | ~l1_orders_2(X5)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f283])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (r2_hidden(X3,X4) | ~r2_hidden(k3_yellow_0(X5),X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5)) | ~sP0(X4,X5) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~r1_yellow_0(X5,k1_xboole_0) | ~l1_orders_2(X5)) )),
% 0.21/0.53    inference(resolution,[],[f87,f228])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f226,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,k3_yellow_0(X0),X1) | ~r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(resolution,[],[f99,f216])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ( ! [X0] : (sP2(k3_yellow_0(X0),X0,k1_xboole_0) | ~r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(resolution,[],[f215,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | sP2(X2,X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | ~r2_lattice3(X1,X0,X2)) & ((sP2(X2,X1,X0) & r2_lattice3(X1,X0,X2)) | ~sP3(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ~sP2(X2,X0,X1) | ~r2_lattice3(X0,X1,X2)) & ((sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)) | ~sP3(X1,X0,X2)))),
% 0.21/0.53    inference(flattening,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | (~sP2(X2,X0,X1) | ~r2_lattice3(X0,X1,X2))) & ((sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)) | ~sP3(X1,X0,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> (sP2(X2,X0,X1) & r2_lattice3(X0,X1,X2)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ( ! [X2] : (sP3(k1_xboole_0,X2,k3_yellow_0(X2)) | ~l1_orders_2(X2) | ~r1_yellow_0(X2,k1_xboole_0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f213,f131])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_yellow_0(X2,k1_xboole_0) | ~m1_subset_1(k3_yellow_0(X2),u1_struct_0(X2)) | ~l1_orders_2(X2) | sP3(k1_xboole_0,X2,k3_yellow_0(X2))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f212])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_yellow_0(X2,k1_xboole_0) | ~m1_subset_1(k3_yellow_0(X2),u1_struct_0(X2)) | ~l1_orders_2(X2) | sP3(k1_xboole_0,X2,k3_yellow_0(X2)) | ~l1_orders_2(X2)) )),
% 0.21/0.53    inference(resolution,[],[f103,f200])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ( ! [X0] : (~sP4(k3_yellow_0(X0),X0,k1_xboole_0) | sP3(k1_xboole_0,X0,k3_yellow_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(superposition,[],[f118,f82])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~sP4(k1_yellow_0(X1,X2),X1,X2) | sP3(X2,X1,k1_yellow_0(X1,X2))) )),
% 0.21/0.53    inference(equality_resolution,[],[f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | k1_yellow_0(X1,X2) != X0 | ~sP4(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((k1_yellow_0(X1,X2) = X0 | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | k1_yellow_0(X1,X2) != X0)) | ~sP4(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ! [X2,X0,X1] : (((k1_yellow_0(X0,X1) = X2 | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | k1_yellow_0(X0,X1) != X2)) | ~sP4(X2,X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X2,X0,X1] : ((k1_yellow_0(X0,X1) = X2 <=> sP3(X1,X0,X2)) | ~sP4(X2,X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (sP4(X2,X0,X1) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(definition_folding,[],[f22,f39,f38,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r1_orders_2(X1,X0,sK10(X0,X1,X2)) & r2_lattice3(X1,X2,sK10(X0,X1,X2)) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f60,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X0,sK10(X0,X1,X2)) & r2_lattice3(X1,X2,sK10(X0,X1,X2)) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X0,X3) & r2_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X0,X4) | ~r2_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X2,X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f37])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X4,X0,X5,X1] : (~r1_orders_2(X1,X4,X5) | r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK9(X0,X1),X0) & r1_orders_2(X1,sK8(X0,X1),sK9(X0,X1)) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(sK9(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f50,f52,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK8(X0,X1),X3) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK8(X0,X1),X3) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK9(X0,X1),X0) & r1_orders_2(X1,sK8(X0,X1),sK9(X0,X1)) & r2_hidden(sK8(X0,X1),X0) & m1_subset_1(sK9(X0,X1),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f34])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    spl13_1 | spl13_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    $false | (spl13_1 | spl13_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f75])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~l1_orders_2(sK6) | (spl13_1 | spl13_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f153,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ~m1_subset_1(k3_yellow_0(sK6),sK7) | spl13_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~v1_xboole_0(sK7)),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    v1_xboole_0(sK7) | ~m1_subset_1(k3_yellow_0(sK6),sK7) | spl13_2),
% 0.21/0.53    inference(resolution,[],[f109,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~r2_hidden(k3_yellow_0(sK6),sK7) | spl13_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    m1_subset_1(k3_yellow_0(sK6),sK7) | ~l1_orders_2(sK6) | spl13_1),
% 0.21/0.53    inference(superposition,[],[f131,f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    u1_struct_0(sK6) = sK7 | spl13_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f123])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ~v1_subset_1(sK7,u1_struct_0(sK6)) | spl13_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    u1_struct_0(sK6) = sK7 | v1_subset_1(sK7,u1_struct_0(sK6))),
% 0.21/0.53    inference(resolution,[],[f111,f79])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl13_1 | ~spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f80,f125,f121])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~spl13_1 | spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f81,f125,f121])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (6496)------------------------------
% 0.21/0.53  % (6496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6496)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (6496)Memory used [KB]: 6396
% 0.21/0.53  % (6496)Time elapsed: 0.109 s
% 0.21/0.53  % (6496)------------------------------
% 0.21/0.53  % (6496)------------------------------
% 0.21/0.53  % (6491)Success in time 0.171 s
%------------------------------------------------------------------------------
