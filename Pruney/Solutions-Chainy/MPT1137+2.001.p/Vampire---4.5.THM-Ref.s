%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:38 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 253 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   16
%              Number of atoms          :  424 (1523 expanded)
%              Number of equality atoms :   30 ( 196 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f119,f170,f178,f188])).

fof(f188,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f186,f41])).

fof(f41,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK3 != sK4
    & r1_orders_2(sK2,sK4,sK3)
    & r1_orders_2(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(sK2,X2,X1)
              & r1_orders_2(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r1_orders_2(sK2,X2,X1)
            & r1_orders_2(sK2,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( sK3 != X2
          & r1_orders_2(sK2,X2,sK3)
          & r1_orders_2(sK2,sK3,X2)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( sK3 != X2
        & r1_orders_2(sK2,X2,sK3)
        & r1_orders_2(sK2,sK3,X2)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( sK3 != sK4
      & r1_orders_2(sK2,sK4,sK3)
      & r1_orders_2(sK2,sK3,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

% (17203)Refutation not found, incomplete strategy% (17203)------------------------------
% (17203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f186,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f185,f40])).

fof(f40,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f185,plain,
    ( ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f184,f86])).

fof(f86,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_3
  <=> r2_hidden(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f184,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f181,f77])).

fof(f77,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_1
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f181,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f163,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r4_relat_2(u1_orders_2(sK2),X0)
        | ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(sK4,X0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_5
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r4_relat_2(u1_orders_2(sK2),X0)
        | ~ r2_hidden(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f178,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f176,f41])).

fof(f176,plain,
    ( ~ l1_orders_2(sK2)
    | spl8_4 ),
    inference(resolution,[],[f175,f93])).

fof(f93,plain,(
    ! [X1] :
      ( v1_relat_1(u1_orders_2(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f56,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f175,plain,
    ( ~ v1_relat_1(u1_orders_2(sK2))
    | spl8_4 ),
    inference(resolution,[],[f160,f55])).

fof(f55,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f23,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X3,X2),X0)
          | ~ r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

fof(f160,plain,
    ( ~ sP1(u1_orders_2(sK2))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl8_4
  <=> sP1(u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f170,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f169,f162,f158])).

fof(f169,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f168,f41])).

fof(f168,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f167,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f167,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f166,f43])).

fof(f43,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f166,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f165,f44])).

fof(f44,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f165,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_orders_2(sK2,sK3,sK4)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f147,f46])).

fof(f46,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f147,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | sK3 = sK4
      | ~ r1_orders_2(sK2,sK3,sK4)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(resolution,[],[f145,f45])).

fof(f45,plain,(
    r1_orders_2(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f145,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X11,X10,X8)
      | ~ r2_hidden(X10,X9)
      | X8 = X10
      | ~ r1_orders_2(X11,X8,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X11))
      | ~ m1_subset_1(X8,u1_struct_0(X11))
      | ~ l1_orders_2(X11)
      | ~ r2_hidden(X8,X9)
      | ~ r4_relat_2(u1_orders_2(X11),X9)
      | ~ sP1(u1_orders_2(X11)) ) ),
    inference(resolution,[],[f142,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r4_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(u1_orders_2(X3),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | X0 = X1
      | ~ r1_orders_2(X3,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r1_orders_2(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ sP0(u1_orders_2(X3),X2)
      | ~ r1_orders_2(X3,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r1_orders_2(X3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f128,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

% (17215)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (17224)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f128,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(k4_tarski(X6,X7),u1_orders_2(X8))
      | X6 = X7
      | ~ r2_hidden(X7,X9)
      | ~ r2_hidden(X6,X9)
      | ~ sP0(u1_orders_2(X8),X9)
      | ~ r1_orders_2(X8,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X8))
      | ~ m1_subset_1(X7,u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) ),
    inference(resolution,[],[f49,f59])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != sK6(X0,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
          & r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK5(X0,X1) != sK6(X0,X1)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f119,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f116,f79])).

fof(f79,plain,
    ( spl8_2
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f116,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f115,f41])).

fof(f115,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f111,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f111,plain,(
    ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f110,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f109,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f107,f43])).

fof(f107,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(resolution,[],[f106,f44])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f59,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f87,plain,
    ( spl8_3
    | spl8_2 ),
    inference(avatar_split_clause,[],[f73,f79,f84])).

fof(f73,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f82,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f72,f79,f75])).

fof(f72,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f64,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:09:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.48  % (17207)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.18/0.48  % (17203)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.48  % (17206)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.18/0.49  % (17206)Refutation found. Thanks to Tanya!
% 0.18/0.49  % SZS status Theorem for theBenchmark
% 0.18/0.49  % (17222)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.18/0.49  % (17214)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.18/0.49  % (17205)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f189,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(avatar_sat_refutation,[],[f82,f87,f119,f170,f178,f188])).
% 0.18/0.49  fof(f188,plain,(
% 0.18/0.49    ~spl8_1 | ~spl8_3 | ~spl8_5),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f187])).
% 0.18/0.49  fof(f187,plain,(
% 0.18/0.49    $false | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.18/0.49    inference(subsumption_resolution,[],[f186,f41])).
% 0.18/0.49  fof(f41,plain,(
% 0.18/0.49    l1_orders_2(sK2)),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    ((sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2)),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f27,f26,f25])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) => (sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  % (17203)Refutation not found, incomplete strategy% (17203)------------------------------
% 0.18/0.49  % (17203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  fof(f12,plain,(
% 0.18/0.49    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0))),
% 0.18/0.49    inference(flattening,[],[f11])).
% 0.18/0.49  fof(f11,plain,(
% 0.18/0.49    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f10])).
% 0.18/0.49  fof(f10,negated_conjecture,(
% 0.18/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.18/0.49    inference(negated_conjecture,[],[f9])).
% 0.18/0.49  fof(f9,conjecture,(
% 0.18/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).
% 0.18/0.49  fof(f186,plain,(
% 0.18/0.49    ~l1_orders_2(sK2) | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.18/0.49    inference(subsumption_resolution,[],[f185,f40])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    v5_orders_2(sK2)),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f185,plain,(
% 0.18/0.49    ~v5_orders_2(sK2) | ~l1_orders_2(sK2) | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.18/0.49    inference(subsumption_resolution,[],[f184,f86])).
% 0.18/0.49  fof(f86,plain,(
% 0.18/0.49    r2_hidden(sK4,u1_struct_0(sK2)) | ~spl8_3),
% 0.18/0.49    inference(avatar_component_clause,[],[f84])).
% 0.18/0.49  fof(f84,plain,(
% 0.18/0.49    spl8_3 <=> r2_hidden(sK4,u1_struct_0(sK2))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.18/0.49  fof(f184,plain,(
% 0.18/0.49    ~r2_hidden(sK4,u1_struct_0(sK2)) | ~v5_orders_2(sK2) | ~l1_orders_2(sK2) | (~spl8_1 | ~spl8_5)),
% 0.18/0.49    inference(subsumption_resolution,[],[f181,f77])).
% 0.18/0.49  fof(f77,plain,(
% 0.18/0.49    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl8_1),
% 0.18/0.49    inference(avatar_component_clause,[],[f75])).
% 0.18/0.49  fof(f75,plain,(
% 0.18/0.49    spl8_1 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.18/0.49  fof(f181,plain,(
% 0.18/0.49    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~r2_hidden(sK4,u1_struct_0(sK2)) | ~v5_orders_2(sK2) | ~l1_orders_2(sK2) | ~spl8_5),
% 0.18/0.49    inference(resolution,[],[f163,f57])).
% 0.18/0.49  fof(f57,plain,(
% 0.18/0.49    ( ! [X0] : (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f34])).
% 0.18/0.49  fof(f34,plain,(
% 0.18/0.49    ! [X0] : (((v5_orders_2(X0) | ~r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.18/0.49    inference(nnf_transformation,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f6])).
% 0.18/0.49  fof(f6,axiom,(
% 0.18/0.49    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).
% 0.18/0.49  fof(f163,plain,(
% 0.18/0.49    ( ! [X0] : (~r4_relat_2(u1_orders_2(sK2),X0) | ~r2_hidden(sK3,X0) | ~r2_hidden(sK4,X0)) ) | ~spl8_5),
% 0.18/0.49    inference(avatar_component_clause,[],[f162])).
% 0.18/0.49  fof(f162,plain,(
% 0.18/0.49    spl8_5 <=> ! [X0] : (~r2_hidden(sK3,X0) | ~r4_relat_2(u1_orders_2(sK2),X0) | ~r2_hidden(sK4,X0))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.18/0.49  fof(f178,plain,(
% 0.18/0.49    spl8_4),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f177])).
% 0.18/0.49  fof(f177,plain,(
% 0.18/0.49    $false | spl8_4),
% 0.18/0.49    inference(subsumption_resolution,[],[f176,f41])).
% 0.18/0.49  fof(f176,plain,(
% 0.18/0.49    ~l1_orders_2(sK2) | spl8_4),
% 0.18/0.49    inference(resolution,[],[f175,f93])).
% 0.18/0.49  fof(f93,plain,(
% 0.18/0.49    ( ! [X1] : (v1_relat_1(u1_orders_2(X1)) | ~l1_orders_2(X1)) )),
% 0.18/0.49    inference(resolution,[],[f56,f65])).
% 0.18/0.49  fof(f65,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.49    inference(ennf_transformation,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.49  fof(f56,plain,(
% 0.18/0.49    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f15])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.18/0.49  fof(f175,plain,(
% 0.18/0.49    ~v1_relat_1(u1_orders_2(sK2)) | spl8_4),
% 0.18/0.49    inference(resolution,[],[f160,f55])).
% 0.18/0.49  fof(f55,plain,(
% 0.18/0.49    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f24])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(definition_folding,[],[f14,f23,f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))),
% 0.18/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.18/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(flattening,[],[f13])).
% 0.18/0.49  fof(f13,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f5])).
% 0.18/0.49  fof(f5,axiom,(
% 0.18/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).
% 0.18/0.49  fof(f160,plain,(
% 0.18/0.49    ~sP1(u1_orders_2(sK2)) | spl8_4),
% 0.18/0.49    inference(avatar_component_clause,[],[f158])).
% 0.18/0.49  fof(f158,plain,(
% 0.18/0.49    spl8_4 <=> sP1(u1_orders_2(sK2))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.18/0.49  fof(f170,plain,(
% 0.18/0.49    ~spl8_4 | spl8_5),
% 0.18/0.49    inference(avatar_split_clause,[],[f169,f162,f158])).
% 0.18/0.49  fof(f169,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f168,f41])).
% 0.18/0.49  fof(f168,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(sK4,X1) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f167,f42])).
% 0.18/0.49  fof(f42,plain,(
% 0.18/0.49    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f167,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(sK4,X1) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f166,f43])).
% 0.18/0.49  fof(f43,plain,(
% 0.18/0.49    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f166,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(sK4,X1) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f165,f44])).
% 0.18/0.49  fof(f44,plain,(
% 0.18/0.49    r1_orders_2(sK2,sK3,sK4)),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f165,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_orders_2(sK2,sK3,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f147,f46])).
% 0.18/0.49  fof(f46,plain,(
% 0.18/0.49    sK3 != sK4),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f147,plain,(
% 0.18/0.49    ( ! [X1] : (~r2_hidden(sK4,X1) | sK3 = sK4 | ~r1_orders_2(sK2,sK3,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.18/0.49    inference(resolution,[],[f145,f45])).
% 0.18/0.49  fof(f45,plain,(
% 0.18/0.49    r1_orders_2(sK2,sK4,sK3)),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f145,plain,(
% 0.18/0.49    ( ! [X10,X8,X11,X9] : (~r1_orders_2(X11,X10,X8) | ~r2_hidden(X10,X9) | X8 = X10 | ~r1_orders_2(X11,X8,X10) | ~m1_subset_1(X10,u1_struct_0(X11)) | ~m1_subset_1(X8,u1_struct_0(X11)) | ~l1_orders_2(X11) | ~r2_hidden(X8,X9) | ~r4_relat_2(u1_orders_2(X11),X9) | ~sP1(u1_orders_2(X11))) )),
% 0.18/0.49    inference(resolution,[],[f142,f47])).
% 0.18/0.49  fof(f47,plain,(
% 0.18/0.49    ( ! [X0,X1] : (sP0(X0,X1) | ~r4_relat_2(X0,X1) | ~sP1(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~r4_relat_2(X0,X1))) | ~sP1(X0))),
% 0.18/0.49    inference(nnf_transformation,[],[f23])).
% 0.18/0.49  fof(f142,plain,(
% 0.18/0.49    ( ! [X2,X0,X3,X1] : (~sP0(u1_orders_2(X3),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | X0 = X1 | ~r1_orders_2(X3,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~r1_orders_2(X3,X0,X1)) )),
% 0.18/0.49    inference(duplicate_literal_removal,[],[f139])).
% 0.18/0.49  fof(f139,plain,(
% 0.18/0.49    ( ! [X2,X0,X3,X1] : (X0 = X1 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~sP0(u1_orders_2(X3),X2) | ~r1_orders_2(X3,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~r1_orders_2(X3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~l1_orders_2(X3)) )),
% 0.18/0.49    inference(resolution,[],[f128,f59])).
% 0.18/0.49  fof(f59,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f35])).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.18/0.49    inference(nnf_transformation,[],[f17])).
% 0.18/0.49  % (17215)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.18/0.49  % (17224)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f7])).
% 0.18/0.49  fof(f7,axiom,(
% 0.18/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.18/0.49  fof(f128,plain,(
% 0.18/0.49    ( ! [X6,X8,X7,X9] : (~r2_hidden(k4_tarski(X6,X7),u1_orders_2(X8)) | X6 = X7 | ~r2_hidden(X7,X9) | ~r2_hidden(X6,X9) | ~sP0(u1_orders_2(X8),X9) | ~r1_orders_2(X8,X7,X6) | ~m1_subset_1(X6,u1_struct_0(X8)) | ~m1_subset_1(X7,u1_struct_0(X8)) | ~l1_orders_2(X8)) )),
% 0.18/0.49    inference(resolution,[],[f49,f59])).
% 0.18/0.49  fof(f49,plain,(
% 0.18/0.49    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X4),X0) | X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~sP0(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f33])).
% 0.18/0.49  fof(f33,plain,(
% 0.18/0.49    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f32])).
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f31,plain,(
% 0.18/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.18/0.49    inference(rectify,[],[f30])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~sP0(X0,X1)))),
% 0.18/0.49    inference(nnf_transformation,[],[f22])).
% 0.18/0.49  fof(f119,plain,(
% 0.18/0.49    ~spl8_2),
% 0.18/0.49    inference(avatar_split_clause,[],[f116,f79])).
% 0.18/0.49  fof(f79,plain,(
% 0.18/0.49    spl8_2 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.18/0.49  fof(f116,plain,(
% 0.18/0.49    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.18/0.49    inference(subsumption_resolution,[],[f115,f41])).
% 0.18/0.49  fof(f115,plain,(
% 0.18/0.49    ~l1_orders_2(sK2) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.18/0.49    inference(resolution,[],[f111,f92])).
% 0.18/0.49  fof(f92,plain,(
% 0.18/0.49    ( ! [X0] : (v1_xboole_0(u1_orders_2(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.18/0.49    inference(resolution,[],[f56,f63])).
% 0.18/0.49  fof(f63,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f18])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.18/0.49  fof(f111,plain,(
% 0.18/0.49    ~v1_xboole_0(u1_orders_2(sK2))),
% 0.18/0.49    inference(subsumption_resolution,[],[f110,f41])).
% 0.18/0.49  fof(f110,plain,(
% 0.18/0.49    ~l1_orders_2(sK2) | ~v1_xboole_0(u1_orders_2(sK2))),
% 0.18/0.49    inference(subsumption_resolution,[],[f109,f42])).
% 0.18/0.49  fof(f109,plain,(
% 0.18/0.49    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v1_xboole_0(u1_orders_2(sK2))),
% 0.18/0.49    inference(subsumption_resolution,[],[f107,f43])).
% 0.18/0.49  fof(f107,plain,(
% 0.18/0.49    ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v1_xboole_0(u1_orders_2(sK2))),
% 0.18/0.49    inference(resolution,[],[f106,f44])).
% 0.18/0.49  fof(f106,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(u1_orders_2(X0))) )),
% 0.18/0.49    inference(resolution,[],[f59,f61])).
% 0.18/0.49  fof(f61,plain,(
% 0.18/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f39])).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 0.18/0.49  fof(f38,plain,(
% 0.18/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f37,plain,(
% 0.18/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.49    inference(rectify,[],[f36])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.49    inference(nnf_transformation,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.49  fof(f87,plain,(
% 0.18/0.49    spl8_3 | spl8_2),
% 0.18/0.49    inference(avatar_split_clause,[],[f73,f79,f84])).
% 0.18/0.49  fof(f73,plain,(
% 0.18/0.49    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK4,u1_struct_0(sK2))),
% 0.18/0.49    inference(resolution,[],[f64,f43])).
% 0.18/0.49  fof(f64,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f20])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.18/0.49    inference(flattening,[],[f19])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.18/0.49    inference(ennf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.18/0.49  fof(f82,plain,(
% 0.18/0.49    spl8_1 | spl8_2),
% 0.18/0.49    inference(avatar_split_clause,[],[f72,f79,f75])).
% 0.18/0.49  fof(f72,plain,(
% 0.18/0.49    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 0.18/0.49    inference(resolution,[],[f64,f42])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (17206)------------------------------
% 0.18/0.49  % (17206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (17206)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (17206)Memory used [KB]: 6140
% 0.18/0.49  % (17206)Time elapsed: 0.099 s
% 0.18/0.49  % (17206)------------------------------
% 0.18/0.49  % (17206)------------------------------
% 0.18/0.50  % (17201)Success in time 0.154 s
%------------------------------------------------------------------------------
