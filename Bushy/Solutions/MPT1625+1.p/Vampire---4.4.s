%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t5_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:00 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 618 expanded)
%              Number of leaves         :   32 ( 200 expanded)
%              Depth                    :   22
%              Number of atoms          :  805 (3470 expanded)
%              Number of equality atoms :   41 ( 193 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2318,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f175,f201,f214,f277,f1742,f2192,f2315])).

fof(f2315,plain,
    ( spl19_1
    | spl19_5
    | ~ spl19_6 ),
    inference(avatar_contradiction_clause,[],[f2314])).

fof(f2314,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f2311,f157])).

fof(f157,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f156])).

fof(f156,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK13(X0,X1) != X0
            | ~ r2_hidden(sK13(X0,X1),X1) )
          & ( sK13(X0,X1) = X0
            | r2_hidden(sK13(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f91,f92])).

fof(f92,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK13(X0,X1) != X0
          | ~ r2_hidden(sK13(X0,X1),X1) )
        & ( sK13(X0,X1) = X0
          | r2_hidden(sK13(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
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
    inference(rectify,[],[f90])).

fof(f90,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',d1_tarski)).

fof(f2311,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f2296,f220])).

fof(f220,plain,(
    r1_orders_2(sK4,sK5,sK5) ),
    inference(subsumption_resolution,[],[f219,f101])).

fof(f101,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
      | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f70,f69])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
              | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),X1),sK4)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),X1),sK4) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),sK5),X0)
          | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),sK5),X0) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
              & v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            & v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',t5_waybel_0)).

fof(f219,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f218,f102])).

fof(f102,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f218,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f217,f103])).

fof(f103,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f217,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f216,f104])).

fof(f104,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f71])).

fof(f216,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f188,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',redefinition_r3_orders_2)).

fof(f188,plain,(
    r3_orders_2(sK4,sK5,sK5) ),
    inference(global_subsumption,[],[f181,f187])).

fof(f187,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | ~ sP17(sK4) ),
    inference(subsumption_resolution,[],[f186,f101])).

fof(f186,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | v2_struct_0(sK4)
    | ~ sP17(sK4) ),
    inference(subsumption_resolution,[],[f185,f102])).

fof(f185,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ sP17(sK4) ),
    inference(subsumption_resolution,[],[f182,f103])).

fof(f182,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ sP17(sK4) ),
    inference(resolution,[],[f104,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP17(X0) ) ),
    inference(general_splitting,[],[f146,f159_D])).

fof(f159,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP17(X0) ) ),
    inference(cnf_transformation,[],[f159_D])).

fof(f159_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP17(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP17])])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',reflexivity_r3_orders_2)).

fof(f181,plain,(
    sP17(sK4) ),
    inference(resolution,[],[f104,f159])).

fof(f2296,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(duplicate_literal_removal,[],[f2295])).

fof(f2295,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r1_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f2294,f504])).

fof(f504,plain,
    ( sK5 = sK6(sK4,k1_tarski(sK5))
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f292,f158])).

fof(f158,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f292,plain,
    ( r2_hidden(sK6(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f280,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
              | ~ r1_orders_2(X0,sK6(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
                  & r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
                  & r2_hidden(sK8(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK8(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f75,f78,f77,f76])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK6(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,X2,X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
            | ~ r1_orders_2(X0,X2,X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
        & r2_hidden(sK8(X0,X1,X5,X6),X1)
        & m1_subset_1(sK8(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f280,plain,
    ( ~ sP0(sK4,k1_tarski(sK5))
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f279,f227])).

fof(f227,plain,
    ( ~ v1_waybel_0(k1_tarski(sK5),sK4)
    | ~ spl19_1
    | ~ spl19_6 ),
    inference(backward_demodulation,[],[f200,f168])).

fof(f168,plain,
    ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl19_1
  <=> ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f200,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | ~ spl19_6 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl19_6
  <=> k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).

fof(f279,plain,
    ( ~ sP0(sK4,k1_tarski(sK5))
    | v1_waybel_0(k1_tarski(sK5),sK4)
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f238,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f238,plain,
    ( sP1(k1_tarski(sK5),sK4)
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f232,f103])).

fof(f232,plain,
    ( sP1(k1_tarski(sK5),sK4)
    | ~ l1_orders_2(sK4)
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f230,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f40,f64,f63])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',d1_waybel_0)).

fof(f230,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f229,f191])).

fof(f191,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ spl19_5 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl19_5
  <=> ~ v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f229,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f228,f104])).

fof(f228,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl19_6 ),
    inference(superposition,[],[f139,f200])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',dt_k6_domain_1)).

fof(f2294,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r1_orders_2(sK4,sK6(sK4,k1_tarski(sK5)),X0)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f2293,f233])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK5))
        | m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f230,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',t4_subset)).

fof(f2293,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r1_orders_2(sK4,sK6(sK4,k1_tarski(sK5)),X0)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f2292,f280])).

fof(f2292,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | sP0(sK4,k1_tarski(sK5))
        | ~ r1_orders_2(sK4,sK6(sK4,k1_tarski(sK5)),X0)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(superposition,[],[f118,f511])).

fof(f511,plain,
    ( sK5 = sK7(sK4,k1_tarski(sK5))
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f293,f158])).

fof(f293,plain,
    ( r2_hidden(sK7(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | ~ spl19_1
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f280,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
      | sP0(X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f2192,plain,
    ( spl19_5
    | ~ spl19_6
    | spl19_17 ),
    inference(avatar_contradiction_clause,[],[f2191])).

fof(f2191,plain,
    ( $false
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_17 ),
    inference(subsumption_resolution,[],[f2188,f157])).

fof(f2188,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_17 ),
    inference(resolution,[],[f1885,f220])).

fof(f1885,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_17 ),
    inference(duplicate_literal_removal,[],[f1884])).

fof(f1884,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK5)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_17 ),
    inference(forward_demodulation,[],[f1883,f1845])).

fof(f1845,plain,
    ( sK5 = sK9(sK4,k1_tarski(sK5))
    | ~ spl19_17 ),
    inference(resolution,[],[f1772,f158])).

fof(f1772,plain,
    ( r2_hidden(sK9(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | ~ spl19_17 ),
    inference(resolution,[],[f266,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
              | ~ r1_orders_2(X0,X4,sK9(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X1)
          & m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X6)
                  & r1_orders_2(X0,sK11(X0,X1,X5,X6),X5)
                  & r2_hidden(sK11(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK11(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f83,f86,f85,f84])).

fof(f84,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK9(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK9(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK11(X0,X1,X5,X6),X5)
        & r2_hidden(sK11(X0,X1,X5,X6),X1)
        & m1_subset_1(sK11(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X7,X6)
                    & r1_orders_2(X0,X7,X5)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f266,plain,
    ( ~ sP2(sK4,k1_tarski(sK5))
    | ~ spl19_17 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl19_17
  <=> ~ sP2(sK4,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_17])])).

fof(f1883,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK9(sK4,k1_tarski(sK5)))
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_17 ),
    inference(subsumption_resolution,[],[f1882,f233])).

fof(f1882,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK9(sK4,k1_tarski(sK5)))
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl19_17 ),
    inference(subsumption_resolution,[],[f1881,f266])).

fof(f1881,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | sP2(sK4,k1_tarski(sK5))
        | ~ r1_orders_2(sK4,X0,sK9(sK4,k1_tarski(sK5)))
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl19_17 ),
    inference(superposition,[],[f130,f1868])).

fof(f1868,plain,
    ( sK5 = sK10(sK4,k1_tarski(sK5))
    | ~ spl19_17 ),
    inference(resolution,[],[f1773,f158])).

fof(f1773,plain,
    ( r2_hidden(sK10(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | ~ spl19_17 ),
    inference(resolution,[],[f266,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
      | sP2(X0,X1)
      | ~ r1_orders_2(X0,X4,sK9(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f1742,plain,
    ( spl19_3
    | ~ spl19_6
    | ~ spl19_18 ),
    inference(avatar_contradiction_clause,[],[f1741])).

fof(f1741,plain,
    ( $false
    | ~ spl19_3
    | ~ spl19_6
    | ~ spl19_18 ),
    inference(subsumption_resolution,[],[f1740,f272])).

fof(f272,plain,
    ( v2_waybel_0(k1_tarski(sK5),sK4)
    | ~ spl19_18 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl19_18
  <=> v2_waybel_0(k1_tarski(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_18])])).

fof(f1740,plain,
    ( ~ v2_waybel_0(k1_tarski(sK5),sK4)
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(forward_demodulation,[],[f174,f200])).

fof(f174,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl19_3
  <=> ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f277,plain,
    ( spl19_18
    | ~ spl19_17
    | spl19_5
    | ~ spl19_6 ),
    inference(avatar_split_clause,[],[f263,f199,f190,f265,f271])).

fof(f263,plain,
    ( ~ sP2(sK4,k1_tarski(sK5))
    | v2_waybel_0(k1_tarski(sK5),sK4)
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f237,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ sP2(X1,X0)
      | v2_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ( v2_waybel_0(X0,X1)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ v2_waybel_0(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ( ( v2_waybel_0(X1,X0)
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ~ v2_waybel_0(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ( v2_waybel_0(X1,X0)
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f237,plain,
    ( sP3(k1_tarski(sK5),sK4)
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f231,f103])).

fof(f231,plain,
    ( sP3(k1_tarski(sK5),sK4)
    | ~ l1_orders_2(sK4)
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f230,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP3(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f42,f67,f66])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',d2_waybel_0)).

fof(f214,plain,(
    ~ spl19_4 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f212,f101])).

fof(f212,plain,
    ( v2_struct_0(sK4)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f209,f176])).

fof(f176,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f103,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',dt_l1_orders_2)).

fof(f209,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ spl19_4 ),
    inference(resolution,[],[f194,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',fc2_struct_0)).

fof(f194,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl19_4
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f201,plain,
    ( spl19_4
    | spl19_6 ),
    inference(avatar_split_clause,[],[f183,f199,f193])).

fof(f183,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f104,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',redefinition_k6_domain_1)).

fof(f175,plain,
    ( ~ spl19_1
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f105,f173,f167])).

fof(f105,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
