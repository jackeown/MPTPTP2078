%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t20_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:45 EDT 2019

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 430 expanded)
%              Number of leaves         :    8 ( 173 expanded)
%              Depth                    :   12
%              Number of atoms          :  255 (3244 expanded)
%              Number of equality atoms :   28 ( 909 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7595,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f232,f233,f237,f234,f235,f7364,f7375,f298])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t20_waybel_0.p',t25_orders_2)).

fof(f7375,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f230,f233,f234,f235,f1771,f290])).

fof(f290,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_waybel_0(X0,X1))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f202])).

fof(f202,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t20_waybel_0.p',t18_waybel_0)).

fof(f1771,plain,(
    r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f235,f846,f561])).

fof(f561,plain,(
    ! [X0] :
      ( r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f560,f230])).

fof(f560,plain,(
    ! [X0] :
      ( r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f559,f233])).

fof(f559,plain,(
    ! [X0] :
      ( r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f558,f235])).

fof(f558,plain,(
    ! [X0] :
      ( r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f291,f236])).

fof(f236,plain,(
    k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,plain,
    ( sK1 != sK2
    & k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f96,f188,f187,f186])).

fof(f186,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(sK0,X1) = k6_waybel_0(sK0,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f187,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK1 != X2
            & k6_waybel_0(X0,sK1) = k6_waybel_0(X0,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2 != X1
        & k6_waybel_0(X0,sK2) = k6_waybel_0(X0,X1)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f95])).

fof(f95,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t20_waybel_0.p',t20_waybel_0)).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f202])).

fof(f846,plain,(
    r1_orders_2(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f230,f231,f233,f235,f235,f533,f318])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f213,plain,(
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
    inference(nnf_transformation,[],[f182])).

fof(f182,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f181])).

fof(f181,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t20_waybel_0.p',redefinition_r3_orders_2)).

fof(f533,plain,(
    r3_orders_2(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f230,f231,f233,f235,f341])).

fof(f341,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f317])).

fof(f317,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f180])).

fof(f180,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f179])).

fof(f179,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t20_waybel_0.p',reflexivity_r3_orders_2)).

fof(f231,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f189])).

fof(f230,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f189])).

fof(f7364,plain,(
    r1_orders_2(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f234,f1770,f557])).

fof(f557,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f556,f230])).

fof(f556,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f555,f233])).

fof(f555,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f554,f235])).

fof(f554,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f290,f236])).

fof(f1770,plain,(
    r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f230,f233,f234,f234,f845,f291])).

fof(f845,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f230,f231,f233,f234,f234,f532,f318])).

fof(f532,plain,(
    r3_orders_2(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f230,f231,f233,f234,f341])).

fof(f235,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f189])).

fof(f234,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f189])).

fof(f237,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f189])).

fof(f233,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f189])).

fof(f232,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f189])).
%------------------------------------------------------------------------------
