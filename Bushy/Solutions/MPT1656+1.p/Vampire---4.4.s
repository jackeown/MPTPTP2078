%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t36_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:49 EDT 2019

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 591 expanded)
%              Number of leaves         :   19 ( 176 expanded)
%              Depth                    :   31
%              Number of atoms          :  840 (4788 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3551,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f139,f3234,f3548])).

fof(f3548,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f3547])).

fof(f3547,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3546,f84])).

fof(f84,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
      | ~ r1_lattice3(sK0,sK1,sK2) )
    & ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
      | r1_lattice3(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f58,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | ~ r1_lattice3(X0,X1,X2) )
                & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | r1_lattice3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,X1),X2)
                | ~ r1_lattice3(sK0,X1,X2) )
              & ( r1_lattice3(sK0,k4_waybel_0(sK0,X1),X2)
                | r1_lattice3(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | ~ r1_lattice3(X0,X1,X2) )
              & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | r1_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,sK1),X2)
              | ~ r1_lattice3(X0,sK1,X2) )
            & ( r1_lattice3(X0,k4_waybel_0(X0,sK1),X2)
              | r1_lattice3(X0,sK1,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
            | ~ r1_lattice3(X0,X1,X2) )
          & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
            | r1_lattice3(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),sK2)
          | ~ r1_lattice3(X0,X1,sK2) )
        & ( r1_lattice3(X0,k4_waybel_0(X0,X1),sK2)
          | r1_lattice3(X0,X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | ~ r1_lattice3(X0,X1,X2) )
              & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | r1_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | ~ r1_lattice3(X0,X1,X2) )
              & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | r1_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <~> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <~> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X2)
                <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',t36_waybel_0)).

fof(f3546,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3545,f86])).

fof(f86,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f3545,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3544,f128])).

fof(f128,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_1
  <=> ~ r1_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f3544,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f3541])).

fof(f3541,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | r1_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_2 ),
    inference(resolution,[],[f3473,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f71,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',d8_lattice3)).

fof(f3473,plain,
    ( ! [X13] :
        ( ~ r2_hidden(sK6(sK0,X13,sK2),sK1)
        | r1_lattice3(sK0,X13,sK2) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3472,f84])).

fof(f3472,plain,
    ( ! [X13] :
        ( ~ r2_hidden(sK6(sK0,X13,sK2),sK1)
        | r1_lattice3(sK0,X13,sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3453,f86])).

fof(f3453,plain,
    ( ! [X13] :
        ( ~ r2_hidden(sK6(sK0,X13,sK2),sK1)
        | r1_lattice3(sK0,X13,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_2 ),
    inference(resolution,[],[f3421,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f3421,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3420,f167])).

fof(f167,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f115,f85])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',t4_subset)).

fof(f3420,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f3398])).

fof(f3398,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f3300,f277])).

fof(f277,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f276,f167])).

fof(f276,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f275,f81])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f275,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f274,f82])).

fof(f82,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f274,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f273,f84])).

fof(f273,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f231,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',redefinition_r3_orders_2)).

fof(f231,plain,(
    ! [X0] :
      ( r3_orders_2(sK0,X0,X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f185,f167])).

fof(f185,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f184,f81])).

fof(f184,plain,(
    ! [X0] :
      ( r3_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f183,f82])).

fof(f183,plain,(
    ! [X0] :
      ( r3_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f84])).

fof(f179,plain,(
    ! [X0] :
      ( r3_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f112,f86])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',reflexivity_r3_orders_2)).

fof(f3300,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,X0)
        | r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f3282])).

fof(f3282,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f3250,f361])).

fof(f361,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X4,X5)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f357,f84])).

fof(f357,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,k4_waybel_0(sK0,sK1))
      | ~ r2_hidden(X4,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f228,f85])).

fof(f228,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r2_hidden(X3,k4_waybel_0(X2,X1))
      | ~ r2_hidden(X0,X1)
      | ~ l1_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f227,f115])).

fof(f227,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_orders_2(X2,X0,X3)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r2_hidden(X3,k4_waybel_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_orders_2(X2) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_orders_2(X2,X0,X3)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r2_hidden(X3,k4_waybel_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f122,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',dt_k4_waybel_0)).

fof(f122,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_hidden(X6,k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,X4,sK3(X0,X1,X2))
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK4(X0,X1,X2),sK3(X0,X1,X2))
                        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK3(X0,X1,X2),X2) )
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X7,X6)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                            & r1_orders_2(X0,sK5(X0,X1,X6),X6)
                            & m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f65,f68,f67,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r1_orders_2(X0,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r1_orders_2(X0,X5,X3)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r1_orders_2(X0,X4,sK3(X0,X1,X2))
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,X5,sK3(X0,X1,X2))
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,X5,X3)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r1_orders_2(X0,sK4(X0,X1,X2),X3)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X8,X6)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r1_orders_2(X0,sK5(X0,X1,X6),X6)
        & m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r1_orders_2(X0,X5,X3)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X7,X6)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ? [X8] :
                              ( r2_hidden(X8,X1)
                              & r1_orders_2(X0,X8,X6)
                              & m1_subset_1(X8,u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X4,X3)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X4,X3)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X4,X3)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X4,X3)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X4,X3)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X4,X3)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',d16_waybel_0)).

fof(f3250,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3249,f84])).

fof(f3249,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3244,f86])).

fof(f3244,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_2 ),
    inference(resolution,[],[f138,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f138,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_2
  <=> r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f3234,plain,
    ( ~ spl10_0
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f3233])).

fof(f3233,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f3232,f84])).

fof(f3232,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f3231,f86])).

fof(f3231,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f3230,f131])).

fof(f131,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl10_3
  <=> ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f3230,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_0 ),
    inference(duplicate_literal_removal,[],[f3223])).

fof(f3223,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_0 ),
    inference(resolution,[],[f1574,f103])).

fof(f1574,plain,
    ( ! [X17,X18] :
        ( r1_orders_2(sK0,sK2,sK6(X17,k4_waybel_0(sK0,sK1),X18))
        | r1_lattice3(X17,k4_waybel_0(sK0,sK1),X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
    | ~ spl10_0 ),
    inference(resolution,[],[f1435,f102])).

fof(f1435,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1434,f84])).

fof(f1434,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1433,f85])).

fof(f1433,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(duplicate_literal_removal,[],[f1432])).

fof(f1432,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(resolution,[],[f1120,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X1,X2,X0),X2)
      | ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f202,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_waybel_0(X1,X0))
      | ~ l1_orders_2(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f109,f115])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(sK5(X1,X2,X0),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(sK5(X1,X2,X0),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f123,f109])).

fof(f123,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X6),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1120,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK5(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,sK2,X8)
        | ~ r2_hidden(X8,k4_waybel_0(sK0,X7)) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1119,f83])).

fof(f83,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f1119,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK5(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,sK2,X8)
        | ~ r2_hidden(X8,k4_waybel_0(sK0,X7))
        | ~ v4_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1118,f86])).

fof(f1118,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK5(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,sK2,X8)
        | ~ r2_hidden(X8,k4_waybel_0(sK0,X7))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1101,f84])).

fof(f1101,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK5(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,sK2,X8)
        | ~ r2_hidden(X8,k4_waybel_0(sK0,X7))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(resolution,[],[f1091,f332])).

fof(f332,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,X3,sK5(X1,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X3,X0)
      | ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v4_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f331,f215])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
      | ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f214,f169])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f125,f109])).

fof(f125,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f331,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X3,X0)
      | ~ r1_orders_2(X1,X3,sK5(X1,X2,X0))
      | ~ m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v4_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f330,f169])).

fof(f330,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X3,X0)
      | ~ r1_orders_2(X1,X3,sK5(X1,X2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v4_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X3,X0)
      | ~ r1_orders_2(X1,X3,sK5(X1,X2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v4_orders_2(X1) ) ),
    inference(resolution,[],[f212,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t36_waybel_0.p',t26_orders_2)).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK5(X1,X2,X0),X0)
      | ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f211,f169])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r1_orders_2(X1,sK5(X1,X2,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_waybel_0(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r1_orders_2(X1,sK5(X1,X2,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f124,f109])).

fof(f124,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r1_orders_2(X0,sK5(X0,X1,X6),X6)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X6),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1091,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1090,f167])).

fof(f1090,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1089,f84])).

fof(f1089,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f1088,f86])).

fof(f1088,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_0 ),
    inference(resolution,[],[f135,f100])).

fof(f135,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl10_0
  <=> r1_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f139,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f87,f137,f134])).

fof(f87,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | r1_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f132,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f88,f130,f127])).

fof(f88,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ r1_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
