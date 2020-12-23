%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1643+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 33.14s
% Output     : Refutation 33.14s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 500 expanded)
%              Number of leaves         :   24 ( 161 expanded)
%              Depth                    :   16
%              Number of atoms          :  645 (2896 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3458,f3459,f4163,f4169,f4175,f4181,f4192,f14610,f14774,f27655,f28651,f29161])).

fof(f29161,plain,
    ( ~ spl24_2
    | spl24_22
    | ~ spl24_59 ),
    inference(avatar_contradiction_clause,[],[f29160])).

fof(f29160,plain,
    ( $false
    | ~ spl24_2
    | spl24_22
    | ~ spl24_59 ),
    inference(subsumption_resolution,[],[f28725,f5925])).

fof(f5925,plain,
    ( r2_hidden(sK10(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ spl24_59 ),
    inference(avatar_component_clause,[],[f5924])).

fof(f5924,plain,
    ( spl24_59
  <=> r2_hidden(sK10(sK0,sK1),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_59])])).

fof(f28725,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ spl24_2
    | spl24_22 ),
    inference(resolution,[],[f3456,f4293])).

fof(f4293,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r2_hidden(sK10(sK0,sK1),X3) )
    | spl24_22 ),
    inference(resolution,[],[f4162,f3363])).

fof(f3363,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3293])).

fof(f3293,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3291,f3292])).

fof(f3292,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3291,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3290])).

fof(f3290,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3236])).

fof(f3236,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f4162,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),sK1)
    | spl24_22 ),
    inference(avatar_component_clause,[],[f4160])).

fof(f4160,plain,
    ( spl24_22
  <=> r2_hidden(sK10(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_22])])).

fof(f3456,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ spl24_2 ),
    inference(avatar_component_clause,[],[f3455])).

fof(f3455,plain,
    ( spl24_2
  <=> r1_tarski(k3_waybel_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_2])])).

fof(f28651,plain,
    ( spl24_59
    | ~ spl24_23
    | ~ spl24_24
    | ~ spl24_25 ),
    inference(avatar_split_clause,[],[f27943,f4178,f4172,f4166,f5924])).

fof(f4166,plain,
    ( spl24_23
  <=> r1_orders_2(sK0,sK10(sK0,sK1),sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_23])])).

fof(f4172,plain,
    ( spl24_24
  <=> r2_hidden(sK9(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_24])])).

fof(f4178,plain,
    ( spl24_25
  <=> m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_25])])).

fof(f27943,plain,
    ( r2_hidden(sK10(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ spl24_23
    | ~ spl24_24
    | ~ spl24_25 ),
    inference(subsumption_resolution,[],[f27942,f4180])).

fof(f4180,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl24_25 ),
    inference(avatar_component_clause,[],[f4178])).

fof(f27942,plain,
    ( r2_hidden(sK10(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl24_23
    | ~ spl24_24 ),
    inference(subsumption_resolution,[],[f27924,f4174])).

fof(f4174,plain,
    ( r2_hidden(sK9(sK0,sK1),sK1)
    | ~ spl24_24 ),
    inference(avatar_component_clause,[],[f4172])).

fof(f27924,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | r2_hidden(sK10(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl24_23 ),
    inference(subsumption_resolution,[],[f6892,f3533])).

fof(f3533,plain,(
    ! [X29] :
      ( ~ r2_hidden(X29,sK1)
      | m1_subset_1(X29,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f3347,f3399])).

fof(f3399,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3253])).

fof(f3253,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3252])).

fof(f3252,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f3347,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3284])).

fof(f3284,plain,
    ( ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
      | ~ v12_waybel_0(sK1,sK0) )
    & ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
      | v12_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3281,f3283,f3282])).

fof(f3282,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
              | ~ v12_waybel_0(X1,X0) )
            & ( r1_tarski(k3_waybel_0(X0,X1),X1)
              | v12_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(sK0,X1),X1)
            | ~ v12_waybel_0(X1,sK0) )
          & ( r1_tarski(k3_waybel_0(sK0,X1),X1)
            | v12_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3283,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(k3_waybel_0(sK0,X1),X1)
          | ~ v12_waybel_0(X1,sK0) )
        & ( r1_tarski(k3_waybel_0(sK0,X1),X1)
          | v12_waybel_0(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
        | ~ v12_waybel_0(sK1,sK0) )
      & ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
        | v12_waybel_0(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3281,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
            | ~ v12_waybel_0(X1,X0) )
          & ( r1_tarski(k3_waybel_0(X0,X1),X1)
            | v12_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3280])).

fof(f3280,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
            | ~ v12_waybel_0(X1,X0) )
          & ( r1_tarski(k3_waybel_0(X0,X1),X1)
            | v12_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3225])).

fof(f3225,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v12_waybel_0(X1,X0)
          <~> r1_tarski(k3_waybel_0(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3206])).

fof(f3206,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v12_waybel_0(X1,X0)
            <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f3205])).

fof(f3205,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_0)).

fof(f6892,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | r2_hidden(sK10(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl24_23 ),
    inference(resolution,[],[f3563,f4168])).

fof(f4168,plain,
    ( r1_orders_2(sK0,sK10(sK0,sK1),sK9(sK0,sK1))
    | ~ spl24_23 ),
    inference(avatar_component_clause,[],[f4166])).

fof(f3563,plain,(
    ! [X14,X15] :
      ( ~ r1_orders_2(sK0,X14,X15)
      | ~ r2_hidden(X15,sK1)
      | r2_hidden(X14,k3_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3562,f3346])).

fof(f3346,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3284])).

fof(f3562,plain,(
    ! [X14,X15] :
      ( r2_hidden(X14,k3_waybel_0(sK0,sK1))
      | ~ r2_hidden(X15,sK1)
      | ~ r1_orders_2(sK0,X14,X15)
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3518,f3550])).

fof(f3550,plain,(
    m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f3501,f3346])).

fof(f3501,plain,
    ( m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3347,f3375])).

fof(f3375,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3243])).

fof(f3243,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3242])).

fof(f3242,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3169])).

fof(f3169,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_0)).

fof(f3518,plain,(
    ! [X14,X15] :
      ( r2_hidden(X14,k3_waybel_0(sK0,sK1))
      | ~ r2_hidden(X15,sK1)
      | ~ r1_orders_2(sK0,X14,X15)
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3347,f3445])).

fof(f3445,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3379])).

fof(f3379,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3306])).

fof(f3306,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,sK6(X0,X1,X2),X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK6(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
                        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK6(X0,X1,X2),X2) )
                    & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                            & r1_orders_2(X0,X6,sK8(X0,X1,X6))
                            & m1_subset_1(sK8(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f3302,f3305,f3304,f3303])).

fof(f3303,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r1_orders_2(X0,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r1_orders_2(X0,X3,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r1_orders_2(X0,sK6(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,sK6(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK6(X0,X1,X2),X2) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3304,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,sK6(X0,X1,X2),X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r1_orders_2(X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3305,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r1_orders_2(X0,X6,sK8(X0,X1,X6))
        & m1_subset_1(sK8(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3302,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r1_orders_2(X0,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ? [X8] :
                              ( r2_hidden(X8,X1)
                              & r1_orders_2(X0,X6,X8)
                              & m1_subset_1(X8,u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3301])).

fof(f3301,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3300])).

fof(f3300,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3244])).

fof(f3244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3158])).

fof(f3158,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_waybel_0)).

fof(f27655,plain,
    ( spl24_2
    | ~ spl24_27
    | ~ spl24_307
    | ~ spl24_308 ),
    inference(avatar_contradiction_clause,[],[f27654])).

fof(f27654,plain,
    ( $false
    | spl24_2
    | ~ spl24_27
    | ~ spl24_307
    | ~ spl24_308 ),
    inference(subsumption_resolution,[],[f27653,f4452])).

fof(f4452,plain,
    ( ~ r2_hidden(sK3(k3_waybel_0(sK0,sK1),sK1),sK1)
    | spl24_2 ),
    inference(resolution,[],[f3457,f3365])).

fof(f3365,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f3293])).

fof(f3457,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | spl24_2 ),
    inference(avatar_component_clause,[],[f3455])).

fof(f27653,plain,
    ( r2_hidden(sK3(k3_waybel_0(sK0,sK1),sK1),sK1)
    | spl24_2
    | ~ spl24_27
    | ~ spl24_307
    | ~ spl24_308 ),
    inference(subsumption_resolution,[],[f27652,f6094])).

fof(f6094,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)),sK1)
    | spl24_2 ),
    inference(subsumption_resolution,[],[f6062,f3347])).

fof(f6062,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl24_2 ),
    inference(resolution,[],[f3481,f4451])).

fof(f4451,plain,
    ( r2_hidden(sK3(k3_waybel_0(sK0,sK1),sK1),k3_waybel_0(sK0,sK1))
    | spl24_2 ),
    inference(resolution,[],[f3457,f3364])).

fof(f3364,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f3293])).

fof(f3481,plain,(
    ! [X24,X23] :
      ( ~ r2_hidden(X24,k3_waybel_0(sK0,X23))
      | r2_hidden(sK8(sK0,X23,X24),X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3480,f3460])).

fof(f3460,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k3_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3346,f3375])).

fof(f3480,plain,(
    ! [X24,X23] :
      ( r2_hidden(sK8(sK0,X23,X24),X23)
      | ~ r2_hidden(X24,k3_waybel_0(sK0,X23))
      | ~ m1_subset_1(k3_waybel_0(sK0,X23),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3473,f3399])).

fof(f3473,plain,(
    ! [X24,X23] :
      ( r2_hidden(sK8(sK0,X23,X24),X23)
      | ~ r2_hidden(X24,k3_waybel_0(sK0,X23))
      | ~ m1_subset_1(X24,u1_struct_0(sK0))
      | ~ m1_subset_1(k3_waybel_0(sK0,X23),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3346,f3446])).

fof(f3446,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3378])).

fof(f3378,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3306])).

fof(f27652,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)),sK1)
    | r2_hidden(sK3(k3_waybel_0(sK0,sK1),sK1),sK1)
    | ~ spl24_27
    | ~ spl24_307
    | ~ spl24_308 ),
    inference(subsumption_resolution,[],[f27639,f14604])).

fof(f14604,plain,
    ( m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl24_307 ),
    inference(avatar_component_clause,[],[f14603])).

fof(f14603,plain,
    ( spl24_307
  <=> m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_307])])).

fof(f27639,plain,
    ( ~ m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)),sK1)
    | r2_hidden(sK3(k3_waybel_0(sK0,sK1),sK1),sK1)
    | ~ spl24_27
    | ~ spl24_308 ),
    inference(resolution,[],[f14609,f4432])).

fof(f4432,plain,
    ( ! [X12,X13] :
        ( ~ r1_orders_2(sK0,X12,X13)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r2_hidden(X13,sK1)
        | r2_hidden(X12,sK1) )
    | ~ spl24_27 ),
    inference(subsumption_resolution,[],[f4191,f3533])).

fof(f4191,plain,
    ( ! [X12,X13] :
        ( r2_hidden(X12,sK1)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r2_hidden(X13,sK1)
        | ~ r1_orders_2(sK0,X12,X13) )
    | ~ spl24_27 ),
    inference(avatar_component_clause,[],[f4190])).

fof(f4190,plain,
    ( spl24_27
  <=> ! [X13,X12] :
        ( r2_hidden(X12,sK1)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r2_hidden(X13,sK1)
        | ~ r1_orders_2(sK0,X12,X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_27])])).

fof(f14609,plain,
    ( r1_orders_2(sK0,sK3(k3_waybel_0(sK0,sK1),sK1),sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)))
    | ~ spl24_308 ),
    inference(avatar_component_clause,[],[f14607])).

fof(f14607,plain,
    ( spl24_308
  <=> r1_orders_2(sK0,sK3(k3_waybel_0(sK0,sK1),sK1),sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_308])])).

fof(f14774,plain,
    ( spl24_2
    | spl24_307 ),
    inference(avatar_contradiction_clause,[],[f14773])).

fof(f14773,plain,
    ( $false
    | spl24_2
    | spl24_307 ),
    inference(subsumption_resolution,[],[f14759,f4451])).

fof(f14759,plain,
    ( ~ r2_hidden(sK3(k3_waybel_0(sK0,sK1),sK1),k3_waybel_0(sK0,sK1))
    | spl24_307 ),
    inference(resolution,[],[f14605,f4834])).

fof(f4834,plain,(
    ! [X34] :
      ( m1_subset_1(X34,u1_struct_0(sK0))
      | ~ r2_hidden(X34,k3_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3550,f3399])).

fof(f14605,plain,
    ( ~ m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl24_307 ),
    inference(avatar_component_clause,[],[f14603])).

fof(f14610,plain,
    ( ~ spl24_307
    | spl24_308
    | spl24_2 ),
    inference(avatar_split_clause,[],[f14601,f3455,f14607,f14603])).

fof(f14601,plain,
    ( r1_orders_2(sK0,sK3(k3_waybel_0(sK0,sK1),sK1),sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl24_2 ),
    inference(subsumption_resolution,[],[f14600,f3346])).

fof(f14600,plain,
    ( r1_orders_2(sK0,sK3(k3_waybel_0(sK0,sK1),sK1),sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl24_2 ),
    inference(subsumption_resolution,[],[f14599,f3347])).

fof(f14599,plain,
    ( r1_orders_2(sK0,sK3(k3_waybel_0(sK0,sK1),sK1),sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl24_2 ),
    inference(subsumption_resolution,[],[f5020,f3550])).

fof(f5020,plain,
    ( r1_orders_2(sK0,sK3(k3_waybel_0(sK0,sK1),sK1),sK8(sK0,sK1,sK3(k3_waybel_0(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK3(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl24_2 ),
    inference(resolution,[],[f4451,f3447])).

fof(f3447,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,X6,sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3377])).

fof(f3377,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X6,sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3306])).

fof(f4192,plain,
    ( ~ spl24_1
    | spl24_27 ),
    inference(avatar_split_clause,[],[f4188,f4190,f3451])).

fof(f3451,plain,
    ( spl24_1
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_1])])).

fof(f4188,plain,(
    ! [X12,X13] :
      ( r2_hidden(X12,sK1)
      | ~ r1_orders_2(sK0,X12,X13)
      | ~ r2_hidden(X13,sK1)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ v12_waybel_0(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f3512,f3346])).

fof(f3512,plain,(
    ! [X12,X13] :
      ( r2_hidden(X12,sK1)
      | ~ r1_orders_2(sK0,X12,X13)
      | ~ r2_hidden(X13,sK1)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3347,f3385])).

fof(f3385,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3311])).

fof(f3311,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK10(X0,X1),X1)
                & r1_orders_2(X0,sK10(X0,X1),sK9(X0,X1))
                & r2_hidden(sK9(X0,X1),X1)
                & m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f3308,f3310,f3309])).

fof(f3309,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK9(X0,X1))
            & r2_hidden(sK9(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3310,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,sK9(X0,X1))
          & r2_hidden(sK9(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r1_orders_2(X0,sK10(X0,X1),sK9(X0,X1))
        & r2_hidden(sK9(X0,X1),X1)
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3308,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3307])).

fof(f3307,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3246])).

fof(f3246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3245])).

fof(f3245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3162])).

fof(f3162,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f4181,plain,
    ( spl24_25
    | spl24_1 ),
    inference(avatar_split_clause,[],[f4176,f3451,f4178])).

fof(f4176,plain,
    ( v12_waybel_0(sK1,sK0)
    | m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3514,f3346])).

fof(f3514,plain,
    ( v12_waybel_0(sK1,sK0)
    | m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3347,f3387])).

fof(f3387,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3311])).

fof(f4175,plain,
    ( spl24_24
    | spl24_1 ),
    inference(avatar_split_clause,[],[f4170,f3451,f4172])).

fof(f4170,plain,
    ( v12_waybel_0(sK1,sK0)
    | r2_hidden(sK9(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3515,f3346])).

fof(f3515,plain,
    ( v12_waybel_0(sK1,sK0)
    | r2_hidden(sK9(sK0,sK1),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3347,f3388])).

fof(f3388,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r2_hidden(sK9(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3311])).

fof(f4169,plain,
    ( spl24_23
    | spl24_1 ),
    inference(avatar_split_clause,[],[f4164,f3451,f4166])).

fof(f4164,plain,
    ( v12_waybel_0(sK1,sK0)
    | r1_orders_2(sK0,sK10(sK0,sK1),sK9(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3516,f3346])).

fof(f3516,plain,
    ( v12_waybel_0(sK1,sK0)
    | r1_orders_2(sK0,sK10(sK0,sK1),sK9(sK0,sK1))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3347,f3389])).

fof(f3389,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r1_orders_2(X0,sK10(X0,X1),sK9(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3311])).

fof(f4163,plain,
    ( ~ spl24_22
    | spl24_1 ),
    inference(avatar_split_clause,[],[f4158,f3451,f4160])).

fof(f4158,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ r2_hidden(sK10(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3517,f3346])).

fof(f3517,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3347,f3390])).

fof(f3390,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ r2_hidden(sK10(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3311])).

fof(f3459,plain,
    ( spl24_1
    | spl24_2 ),
    inference(avatar_split_clause,[],[f3348,f3455,f3451])).

fof(f3348,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3284])).

fof(f3458,plain,
    ( ~ spl24_1
    | ~ spl24_2 ),
    inference(avatar_split_clause,[],[f3349,f3455,f3451])).

fof(f3349,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3284])).
%------------------------------------------------------------------------------
