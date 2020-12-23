%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 (1858 expanded)
%              Number of leaves         :   25 ( 606 expanded)
%              Depth                    :   16
%              Number of atoms          :  730 (25541 expanded)
%              Number of equality atoms :   47 ( 472 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f105,f109,f113,f117,f168,f206,f214,f222,f230])).

fof(f230,plain,
    ( ~ spl12_1
    | spl12_4
    | ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl12_1
    | spl12_4
    | ~ spl12_6 ),
    inference(unit_resulting_resolution,[],[f100,f228])).

fof(f228,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl12_1
    | spl12_4 ),
    inference(forward_demodulation,[],[f224,f118])).

fof(f118,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f35,f36,f38,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f38,plain,(
    v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
          | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
          | ~ v4_orders_2(k1_funct_1(sK2,sK3))
          | v2_struct_0(k1_funct_1(sK2,sK3)) )
        & r2_hidden(sK3,sK0) )
      | ~ m3_yellow_6(sK2,sK0,sK1) )
    & ( ! [X4] :
          ( ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
            & v7_waybel_0(k1_funct_1(sK2,X4))
            & v4_orders_2(k1_funct_1(sK2,X4))
            & ~ v2_struct_0(k1_funct_1(sK2,X4)) )
          | ~ r2_hidden(X4,sK0) )
      | m3_yellow_6(sK2,sK0,sK1) )
    & v1_partfun1(sK2,sK0)
    & v1_funct_1(sK2)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                    | ~ v7_waybel_0(k1_funct_1(X2,X3))
                    | ~ v4_orders_2(k1_funct_1(X2,X3))
                    | v2_struct_0(k1_funct_1(X2,X3)) )
                  & r2_hidden(X3,X0) )
              | ~ m3_yellow_6(X2,X0,X1) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(k1_funct_1(X2,X4),X1)
                    & v7_waybel_0(k1_funct_1(X2,X4))
                    & v4_orders_2(k1_funct_1(X2,X4))
                    & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                  | ~ r2_hidden(X4,X0) )
              | m3_yellow_6(X2,X0,X1) )
            & v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),sK1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,sK0) )
            | ~ m3_yellow_6(X2,sK0,sK1) )
          & ( ! [X4] :
                ( ( l1_waybel_0(k1_funct_1(X2,X4),sK1)
                  & v7_waybel_0(k1_funct_1(X2,X4))
                  & v4_orders_2(k1_funct_1(X2,X4))
                  & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                | ~ r2_hidden(X4,sK0) )
            | m3_yellow_6(X2,sK0,sK1) )
          & v1_partfun1(X2,sK0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (14165)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (14172)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f20,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),sK1)
                | ~ v7_waybel_0(k1_funct_1(X2,X3))
                | ~ v4_orders_2(k1_funct_1(X2,X3))
                | v2_struct_0(k1_funct_1(X2,X3)) )
              & r2_hidden(X3,sK0) )
          | ~ m3_yellow_6(X2,sK0,sK1) )
        & ( ! [X4] :
              ( ( l1_waybel_0(k1_funct_1(X2,X4),sK1)
                & v7_waybel_0(k1_funct_1(X2,X4))
                & v4_orders_2(k1_funct_1(X2,X4))
                & ~ v2_struct_0(k1_funct_1(X2,X4)) )
              | ~ r2_hidden(X4,sK0) )
          | m3_yellow_6(X2,sK0,sK1) )
        & v1_partfun1(X2,sK0)
        & v1_funct_1(X2)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ( ? [X3] :
            ( ( ~ l1_waybel_0(k1_funct_1(sK2,X3),sK1)
              | ~ v7_waybel_0(k1_funct_1(sK2,X3))
              | ~ v4_orders_2(k1_funct_1(sK2,X3))
              | v2_struct_0(k1_funct_1(sK2,X3)) )
            & r2_hidden(X3,sK0) )
        | ~ m3_yellow_6(sK2,sK0,sK1) )
      & ( ! [X4] :
            ( ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
              & v7_waybel_0(k1_funct_1(sK2,X4))
              & v4_orders_2(k1_funct_1(sK2,X4))
              & ~ v2_struct_0(k1_funct_1(sK2,X4)) )
            | ~ r2_hidden(X4,sK0) )
        | m3_yellow_6(sK2,sK0,sK1) )
      & v1_partfun1(sK2,sK0)
      & v1_funct_1(sK2)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ( ~ l1_waybel_0(k1_funct_1(sK2,X3),sK1)
          | ~ v7_waybel_0(k1_funct_1(sK2,X3))
          | ~ v4_orders_2(k1_funct_1(sK2,X3))
          | v2_struct_0(k1_funct_1(sK2,X3)) )
        & r2_hidden(X3,sK0) )
   => ( ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
        | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
        | ~ v4_orders_2(k1_funct_1(sK2,sK3))
        | v2_struct_0(k1_funct_1(sK2,sK3)) )
      & r2_hidden(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X4] :
                ( ( l1_waybel_0(k1_funct_1(X2,X4),X1)
                  & v7_waybel_0(k1_funct_1(X2,X4))
                  & v4_orders_2(k1_funct_1(X2,X4))
                  & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                | ~ r2_hidden(X4,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( v1_partfun1(X2,X0)
              & v1_funct_1(X2)
              & v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( m3_yellow_6(X2,X0,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                    & v7_waybel_0(k1_funct_1(X2,X3))
                    & v4_orders_2(k1_funct_1(X2,X3))
                    & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,X0)
               => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_yellow_6)).

fof(f36,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f224,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl12_1
    | spl12_4 ),
    inference(unit_resulting_resolution,[],[f35,f37,f223,f64])).

fof(f64,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f223,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl12_1
    | spl12_4 ),
    inference(unit_resulting_resolution,[],[f178,f91,f70])).

fof(f70,plain,(
    ! [X4,X2] :
      ( v7_waybel_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | sP9(X2) ) ),
    inference(cnf_transformation,[],[f70_D])).

fof(f70_D,plain,(
    ! [X2] :
      ( ! [X4] :
          ( v7_waybel_0(X4)
          | ~ r2_hidden(X4,k2_relat_1(X2)) )
    <=> ~ sP9(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f91,plain,
    ( ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | spl12_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl12_4
  <=> v7_waybel_0(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f178,plain,
    ( ~ sP9(sK2)
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f37,f36,f38,f78,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1)
      | ~ sP9(X2) ) ),
    inference(general_splitting,[],[f57,f70_D])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( v7_waybel_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ( ( ~ l1_waybel_0(sK7(X1,X2),X1)
                  | ~ v7_waybel_0(sK7(X1,X2))
                  | ~ v4_orders_2(sK7(X1,X2))
                  | v2_struct_0(sK7(X1,X2)) )
                & r2_hidden(sK7(X1,X2),k2_relat_1(X2)) ) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(X4,X1)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X4,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ( ~ l1_waybel_0(X3,X1)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
          & r2_hidden(X3,k2_relat_1(X2)) )
     => ( ( ~ l1_waybel_0(sK7(X1,X2),X1)
          | ~ v7_waybel_0(sK7(X1,X2))
          | ~ v4_orders_2(sK7(X1,X2))
          | v2_struct_0(sK7(X1,X2)) )
        & r2_hidden(sK7(X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ? [X3] :
                  ( ( ~ l1_waybel_0(X3,X1)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                  & r2_hidden(X3,k2_relat_1(X2)) ) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(X4,X1)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X4,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ? [X3] :
                  ( ( ~ l1_waybel_0(X3,X1)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                  & r2_hidden(X3,k2_relat_1(X2)) ) )
            & ( ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X3,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k2_relat_1(X2))
               => ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_yellow_6)).

fof(f78,plain,
    ( m3_yellow_6(sK2,sK0,sK1)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl12_1
  <=> m3_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl12_6
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f222,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_6 ),
    inference(unit_resulting_resolution,[],[f100,f220])).

fof(f220,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f216,f118])).

fof(f216,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f35,f37,f215,f64])).

fof(f215,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f180,f83,f74])).

fof(f74,plain,(
    ! [X4,X2] :
      ( ~ v2_struct_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | sP11(X2) ) ),
    inference(cnf_transformation,[],[f74_D])).

fof(f74_D,plain,(
    ! [X2] :
      ( ! [X4] :
          ( ~ v2_struct_0(X4)
          | ~ r2_hidden(X4,k2_relat_1(X2)) )
    <=> ~ sP11(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f83,plain,
    ( v2_struct_0(k1_funct_1(sK2,sK3))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl12_2
  <=> v2_struct_0(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f180,plain,
    ( ~ sP11(sK2)
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f37,f36,f38,f78,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1)
      | ~ sP11(X2) ) ),
    inference(general_splitting,[],[f55,f74_D])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_struct_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f214,plain,
    ( ~ spl12_1
    | spl12_3
    | ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl12_1
    | spl12_3
    | ~ spl12_6 ),
    inference(unit_resulting_resolution,[],[f100,f212])).

fof(f212,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl12_1
    | spl12_3 ),
    inference(forward_demodulation,[],[f208,f118])).

fof(f208,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl12_1
    | spl12_3 ),
    inference(unit_resulting_resolution,[],[f35,f37,f207,f64])).

fof(f207,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl12_1
    | spl12_3 ),
    inference(unit_resulting_resolution,[],[f179,f87,f72])).

fof(f72,plain,(
    ! [X4,X2] :
      ( v4_orders_2(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | sP10(X2) ) ),
    inference(cnf_transformation,[],[f72_D])).

fof(f72_D,plain,(
    ! [X2] :
      ( ! [X4] :
          ( v4_orders_2(X4)
          | ~ r2_hidden(X4,k2_relat_1(X2)) )
    <=> ~ sP10(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f87,plain,
    ( ~ v4_orders_2(k1_funct_1(sK2,sK3))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl12_3
  <=> v4_orders_2(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f179,plain,
    ( ~ sP10(sK2)
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f37,f36,f38,f78,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1)
      | ~ sP10(X2) ) ),
    inference(general_splitting,[],[f56,f72_D])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_orders_2(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f206,plain,
    ( ~ spl12_1
    | spl12_5
    | ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl12_1
    | spl12_5
    | ~ spl12_6 ),
    inference(unit_resulting_resolution,[],[f100,f204])).

fof(f204,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl12_1
    | spl12_5 ),
    inference(forward_demodulation,[],[f200,f118])).

fof(f200,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl12_1
    | spl12_5 ),
    inference(unit_resulting_resolution,[],[f35,f37,f199,f64])).

fof(f199,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl12_1
    | spl12_5 ),
    inference(unit_resulting_resolution,[],[f177,f95,f68])).

fof(f68,plain,(
    ! [X4,X2,X1] :
      ( l1_waybel_0(X4,X1)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | sP8(X2,X1) ) ),
    inference(cnf_transformation,[],[f68_D])).

fof(f68_D,plain,(
    ! [X1,X2] :
      ( ! [X4] :
          ( l1_waybel_0(X4,X1)
          | ~ r2_hidden(X4,k2_relat_1(X2)) )
    <=> ~ sP8(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f95,plain,
    ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl12_5
  <=> l1_waybel_0(k1_funct_1(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f177,plain,
    ( ~ sP8(sK2,sK1)
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f37,f34,f35,f36,f38,f78,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1)
      | ~ sP8(X2,X1) ) ),
    inference(general_splitting,[],[f58,f68_D])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( l1_waybel_0(X4,X1)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f168,plain,
    ( spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl12_1
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10 ),
    inference(unit_resulting_resolution,[],[f34,f35,f37,f36,f38,f79,f148,f147,f146,f155,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m3_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(sK7(X1,X2),X1)
      | ~ v7_waybel_0(sK7(X1,X2))
      | ~ v4_orders_2(sK7(X1,X2))
      | v2_struct_0(sK7(X1,X2))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f155,plain,
    ( l1_waybel_0(sK7(sK1,sK2),sK1)
    | spl12_1
    | ~ spl12_7 ),
    inference(forward_demodulation,[],[f152,f132])).

fof(f132,plain,
    ( sK7(sK1,sK2) = k1_funct_1(sK2,sK6(sK2,sK7(sK1,sK2)))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f35,f37,f119,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,
    ( r2_hidden(sK7(sK1,sK2),k2_relat_1(sK2))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f37,f36,f38,f79,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m3_yellow_6(X2,X0,X1)
      | r2_hidden(sK7(X1,X2),k2_relat_1(X2))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f152,plain,
    ( l1_waybel_0(k1_funct_1(sK2,sK6(sK2,sK7(sK1,sK2))),sK1)
    | spl12_1
    | ~ spl12_7 ),
    inference(unit_resulting_resolution,[],[f136,f104])).

fof(f104,plain,
    ( ! [X4] :
        ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl12_7
  <=> ! [X4] :
        ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f136,plain,
    ( r2_hidden(sK6(sK2,sK7(sK1,sK2)),sK0)
    | spl12_1 ),
    inference(forward_demodulation,[],[f131,f118])).

fof(f131,plain,
    ( r2_hidden(sK6(sK2,sK7(sK1,sK2)),k1_relat_1(sK2))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f35,f37,f119,f66])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f146,plain,
    ( v7_waybel_0(sK7(sK1,sK2))
    | spl12_1
    | ~ spl12_8 ),
    inference(forward_demodulation,[],[f145,f132])).

fof(f145,plain,
    ( v7_waybel_0(k1_funct_1(sK2,sK6(sK2,sK7(sK1,sK2))))
    | spl12_1
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f136,f108])).

fof(f108,plain,
    ( ! [X4] :
        ( v7_waybel_0(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl12_8
  <=> ! [X4] :
        ( v7_waybel_0(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f147,plain,
    ( v4_orders_2(sK7(sK1,sK2))
    | spl12_1
    | ~ spl12_9 ),
    inference(forward_demodulation,[],[f144,f132])).

fof(f144,plain,
    ( v4_orders_2(k1_funct_1(sK2,sK6(sK2,sK7(sK1,sK2))))
    | spl12_1
    | ~ spl12_9 ),
    inference(unit_resulting_resolution,[],[f136,f112])).

fof(f112,plain,
    ( ! [X4] :
        ( v4_orders_2(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl12_9
  <=> ! [X4] :
        ( v4_orders_2(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f148,plain,
    ( ~ v2_struct_0(sK7(sK1,sK2))
    | spl12_1
    | ~ spl12_10 ),
    inference(forward_demodulation,[],[f143,f132])).

fof(f143,plain,
    ( ~ v2_struct_0(k1_funct_1(sK2,sK6(sK2,sK7(sK1,sK2))))
    | spl12_1
    | ~ spl12_10 ),
    inference(unit_resulting_resolution,[],[f136,f116])).

fof(f116,plain,
    ( ! [X4] :
        ( ~ v2_struct_0(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl12_10
  <=> ! [X4] :
        ( ~ v2_struct_0(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f79,plain,
    ( ~ m3_yellow_6(sK2,sK0,sK1)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f117,plain,
    ( spl12_1
    | spl12_10 ),
    inference(avatar_split_clause,[],[f39,f115,f77])).

fof(f39,plain,(
    ! [X4] :
      ( ~ v2_struct_0(k1_funct_1(sK2,X4))
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f113,plain,
    ( spl12_1
    | spl12_9 ),
    inference(avatar_split_clause,[],[f40,f111,f77])).

fof(f40,plain,(
    ! [X4] :
      ( v4_orders_2(k1_funct_1(sK2,X4))
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,
    ( spl12_1
    | spl12_8 ),
    inference(avatar_split_clause,[],[f41,f107,f77])).

fof(f41,plain,(
    ! [X4] :
      ( v7_waybel_0(k1_funct_1(sK2,X4))
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,
    ( spl12_1
    | spl12_7 ),
    inference(avatar_split_clause,[],[f42,f103,f77])).

fof(f42,plain,(
    ! [X4] :
      ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,
    ( ~ spl12_1
    | spl12_6 ),
    inference(avatar_split_clause,[],[f43,f98,f77])).

fof(f43,plain,
    ( r2_hidden(sK3,sK0)
    | ~ m3_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,
    ( ~ spl12_1
    | spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f44,f93,f89,f85,f81,f77])).

fof(f44,plain,
    ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | ~ v4_orders_2(k1_funct_1(sK2,sK3))
    | v2_struct_0(k1_funct_1(sK2,sK3))
    | ~ m3_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
