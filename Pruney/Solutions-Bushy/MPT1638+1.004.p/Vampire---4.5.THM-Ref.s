%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1638+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:13 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 389 expanded)
%              Number of leaves         :   40 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  758 (1761 expanded)
%              Number of equality atoms :   88 ( 174 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f110,f112,f134,f145,f150,f166,f201,f221,f225,f245,f259,f263,f273,f311,f343,f368,f400,f411,f428,f451,f474,f495])).

fof(f495,plain,
    ( spl6_6
    | ~ spl6_39
    | ~ spl6_45 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | spl6_6
    | ~ spl6_39
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f488,f108])).

fof(f108,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_6
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f488,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_39
    | ~ spl6_45 ),
    inference(backward_demodulation,[],[f427,f481])).

fof(f481,plain,
    ( sK1 = sK5(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_45 ),
    inference(resolution,[],[f473,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f473,plain,
    ( r2_hidden(sK5(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl6_45
  <=> r2_hidden(sK5(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f427,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl6_39
  <=> r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f474,plain,
    ( spl6_45
    | ~ spl6_5
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f465,f449,f103,f471])).

fof(f103,plain,
    ( spl6_5
  <=> r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f449,plain,
    ( spl6_41
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f465,plain,
    ( r2_hidden(sK5(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl6_5
    | ~ spl6_41 ),
    inference(resolution,[],[f450,f105])).

fof(f105,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f450,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1)) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f449])).

fof(f451,plain,
    ( spl6_41
    | ~ spl6_12
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f292,f270,f261,f163,f449])).

fof(f163,plain,
    ( spl6_12
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f261,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f270,plain,
    ( spl6_25
  <=> k6_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1)) )
    | ~ spl6_12
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f290,f165])).

fof(f165,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1)) )
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(superposition,[],[f262,f272])).

fof(f272,plain,
    ( k6_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f270])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f261])).

fof(f428,plain,
    ( spl6_39
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f420,f397,f270,f163,f103,f84,f79,f425])).

fof(f79,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( spl6_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f397,plain,
    ( spl6_38
  <=> sK2 = sK4(sK2,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

% (26837)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f420,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f419,f105])).

fof(f419,plain,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f418,f272])).

fof(f418,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f417,f81])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f417,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f416,f86])).

fof(f86,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f416,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f414,f165])).

fof(f414,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_38 ),
    inference(superposition,[],[f70,f399])).

fof(f399,plain,
    ( sK2 = sK4(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f397])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X2)
            & r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2))
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,X6,sK4(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X6,sK4(X0,X1,X2))
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X2)
        & r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

fof(f411,plain,
    ( spl6_5
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl6_5
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f409,f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f409,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f408,f272])).

fof(f408,plain,
    ( r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl6_12
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f406,f165])).

fof(f406,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl6_30 ),
    inference(resolution,[],[f342,f75])).

fof(f75,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

% (26830)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f342,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl6_30
  <=> ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f400,plain,
    ( spl6_38
    | ~ spl6_5
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f395,f366,f103,f397])).

fof(f366,plain,
    ( spl6_34
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f395,plain,
    ( sK2 = sK4(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_5
    | ~ spl6_34 ),
    inference(resolution,[],[f367,f105])).

fof(f367,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f366])).

fof(f368,plain,
    ( spl6_34
    | ~ spl6_12
    | ~ spl6_23
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f293,f270,f257,f163,f366])).

fof(f257,plain,
    ( spl6_23
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f293,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 )
    | ~ spl6_12
    | ~ spl6_23
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f291,f165])).

fof(f291,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 )
    | ~ spl6_23
    | ~ spl6_25 ),
    inference(superposition,[],[f258,f272])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0 )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f257])).

fof(f343,plain,
    ( spl6_30
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f319,f309,f107,f94,f341])).

fof(f94,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f309,plain,
    ( spl6_26
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_1_waybel_0(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f317,f96])).

fof(f96,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) )
    | ~ spl6_6
    | ~ spl6_26 ),
    inference(resolution,[],[f310,f109])).

fof(f109,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f310,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X2)
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_1_waybel_0(sK0,X1)) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f309])).

fof(f311,plain,
    ( spl6_26
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f181,f84,f79,f309])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_1_waybel_0(sK0,X1)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f180,f81])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_1_waybel_0(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f178,f86])).

fof(f178,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(X3,a_2_1_waybel_0(X1,X2))
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f77,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f77,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f273,plain,
    ( spl6_25
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f266,f242,f218,f270])).

fof(f218,plain,
    ( spl6_18
  <=> a_2_1_waybel_0(sK0,k1_tarski(sK1)) = k4_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f242,plain,
    ( spl6_21
  <=> k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f266,plain,
    ( k6_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f220,f244])).

fof(f244,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f242])).

fof(f220,plain,
    ( a_2_1_waybel_0(sK0,k1_tarski(sK1)) = k4_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f263,plain,
    ( spl6_24
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f161,f84,f79,f261])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f160,f81])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f71,f86])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f259,plain,
    ( spl6_23
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f156,f84,f79,f257])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0 )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f155,f81])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f68,f86])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK4(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

% (26839)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f245,plain,
    ( spl6_21
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f235,f223,f131,f89,f242])).

fof(f89,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f131,plain,
    ( spl6_10
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f223,plain,
    ( spl6_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_waybel_0(sK0,X0) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f235,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f231,f133])).

fof(f133,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f231,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl6_3
    | ~ spl6_19 ),
    inference(resolution,[],[f224,f91])).

fof(f91,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_waybel_0(sK0,X0) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl6_19
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f154,f84,f79,f223])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_waybel_0(sK0,X0) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f153,f81])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k6_waybel_0(sK0,X0) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f57,f86])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_0)).

fof(f221,plain,
    ( spl6_18
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f207,f199,f163,f218])).

fof(f199,plain,
    ( spl6_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,X0) = a_2_1_waybel_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f207,plain,
    ( a_2_1_waybel_0(sK0,k1_tarski(sK1)) = k4_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f200,f165])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,X0) = a_2_1_waybel_0(sK0,X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( spl6_16
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f152,f84,f79,f199])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,X0) = a_2_1_waybel_0(sK0,X0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f151,f81])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,X0) = a_2_1_waybel_0(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f58,f86])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_0)).

fof(f166,plain,
    ( spl6_12
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f159,f131,f127,f89,f163])).

fof(f127,plain,
    ( spl6_9
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f159,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f158,f128])).

fof(f128,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f158,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f157,f91])).

fof(f157,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(superposition,[],[f62,f133])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f150,plain,
    ( ~ spl6_2
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl6_2
    | spl6_11 ),
    inference(subsumption_resolution,[],[f147,f86])).

fof(f147,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_11 ),
    inference(resolution,[],[f144,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f144,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f145,plain,
    ( ~ spl6_11
    | spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f138,f127,f79,f142])).

fof(f138,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f137,f81])).

fof(f137,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f129,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f129,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f134,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f123,f89,f131,f127])).

fof(f123,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f61,f91])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f112,plain,
    ( ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f111,f107,f103])).

fof(f111,plain,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f54,f109])).

fof(f54,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
    & ( r1_orders_2(sK0,sK1,sK2)
      | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & ( r1_orders_2(X0,X1,X2)
                  | r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(sK0,X1)) )
              & ( r1_orders_2(sK0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_orders_2(sK0,X1,X2)
              | ~ r2_hidden(X2,k6_waybel_0(sK0,X1)) )
            & ( r1_orders_2(sK0,X1,X2)
              | r2_hidden(X2,k6_waybel_0(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_orders_2(sK0,sK1,X2)
            | ~ r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
          & ( r1_orders_2(sK0,sK1,X2)
            | r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r1_orders_2(sK0,sK1,X2)
          | ~ r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
        & ( r1_orders_2(sK0,sK1,X2)
          | r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_orders_2(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
      & ( r1_orders_2(sK0,sK1,sK2)
        | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k6_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f110,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f53,f107,f103])).

fof(f53,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f51,f89])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f50,f84])).

fof(f50,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f79])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
