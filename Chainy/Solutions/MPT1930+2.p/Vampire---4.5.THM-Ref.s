%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1930+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 125 expanded)
%              Number of leaves         :    8 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  156 ( 952 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5211,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5206,f5191])).

fof(f5191,plain,(
    ! [X0] : ~ r1_waybel_0(sK10,sK11,k6_subset_1(X0,sK12)) ),
    inference(unit_resulting_resolution,[],[f4550,f4551,f4552,f4553,f4554,f5135,f4555,f4556,f4575])).

fof(f4575,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3916])).

fof(f3916,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3915])).

fof(f3915,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3887])).

fof(f3887,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

fof(f4556,plain,(
    r1_waybel_0(sK10,sK11,sK12) ),
    inference(cnf_transformation,[],[f4252])).

fof(f4252,plain,
    ( ~ r2_waybel_0(sK10,sK11,sK12)
    & r1_waybel_0(sK10,sK11,sK12)
    & l1_waybel_0(sK11,sK10)
    & v7_waybel_0(sK11)
    & v4_orders_2(sK11)
    & ~ v2_struct_0(sK11)
    & l1_struct_0(sK10)
    & ~ v2_struct_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f3902,f4251,f4250,f4249])).

fof(f4249,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_waybel_0(X0,X1,X2)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(sK10,X1,X2)
              & r1_waybel_0(sK10,X1,X2) )
          & l1_waybel_0(X1,sK10)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK10)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f4250,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_waybel_0(sK10,X1,X2)
            & r1_waybel_0(sK10,X1,X2) )
        & l1_waybel_0(X1,sK10)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_waybel_0(sK10,sK11,X2)
          & r1_waybel_0(sK10,sK11,X2) )
      & l1_waybel_0(sK11,sK10)
      & v7_waybel_0(sK11)
      & v4_orders_2(sK11)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f4251,plain,
    ( ? [X2] :
        ( ~ r2_waybel_0(sK10,sK11,X2)
        & r1_waybel_0(sK10,sK11,X2) )
   => ( ~ r2_waybel_0(sK10,sK11,sK12)
      & r1_waybel_0(sK10,sK11,sK12) ) ),
    introduced(choice_axiom,[])).

fof(f3902,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3901])).

fof(f3901,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3890])).

fof(f3890,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
               => r2_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f3889])).

fof(f3889,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow_6)).

fof(f4555,plain,(
    l1_waybel_0(sK11,sK10) ),
    inference(cnf_transformation,[],[f4252])).

fof(f5135,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f4842,f4677])).

fof(f4677,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f4842,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f4554,plain,(
    v7_waybel_0(sK11) ),
    inference(cnf_transformation,[],[f4252])).

fof(f4553,plain,(
    v4_orders_2(sK11) ),
    inference(cnf_transformation,[],[f4252])).

fof(f4552,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f4252])).

fof(f4551,plain,(
    l1_struct_0(sK10) ),
    inference(cnf_transformation,[],[f4252])).

fof(f4550,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f4252])).

fof(f5206,plain,(
    r1_waybel_0(sK10,sK11,k6_subset_1(u1_struct_0(sK10),sK12)) ),
    inference(unit_resulting_resolution,[],[f4550,f4551,f4552,f4555,f4557,f4568])).

fof(f4568,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4259])).

fof(f4259,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3910])).

fof(f3910,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3909])).

fof(f3909,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3248])).

fof(f3248,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f4557,plain,(
    ~ r2_waybel_0(sK10,sK11,sK12) ),
    inference(cnf_transformation,[],[f4252])).
%------------------------------------------------------------------------------
