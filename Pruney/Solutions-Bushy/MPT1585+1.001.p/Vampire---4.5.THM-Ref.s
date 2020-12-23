%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1585+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:09 EST 2020

% Result     : Theorem 5.71s
% Output     : Refutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  258 (24621 expanded)
%              Number of leaves         :   29 (8769 expanded)
%              Depth                    :   77
%              Number of atoms          : 1307 (230541 expanded)
%              Number of equality atoms :   96 (21646 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3547,plain,(
    $false ),
    inference(subsumption_resolution,[],[f83,f3545])).

fof(f3545,plain,(
    ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK6)) ),
    inference(resolution,[],[f3543,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f3543,plain,(
    v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f3542,f152])).

fof(f152,plain,(
    r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f150,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_orders_2(X1,sK12(X0,X1,X2),X0)
          & r1_lattice3(X1,X2,sK12(X0,X1,X2))
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r1_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X4,X0)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X0) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK12(X0,X1,X2),X0)
        & r1_lattice3(X1,X2,sK12(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X3,X0)
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ r1_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X4,X0)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X0) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r1_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X3,X2)
              | ~ r1_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r1_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X3,X2)
              | ~ r1_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f150,plain,(
    sP3(k2_yellow_0(sK5,sK7),sK5,sK7) ),
    inference(resolution,[],[f149,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1,k2_yellow_0(X1,X0))
      | sP3(k2_yellow_0(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k2_yellow_0(X1,X0) != X2
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_yellow_0(X1,X0) = X2
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | k2_yellow_0(X1,X0) != X2 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X1,X0,X2] :
      ( ( ( k2_yellow_0(X0,X1) = X2
          | ~ sP3(X2,X0,X1) )
        & ( sP3(X2,X0,X1)
          | k2_yellow_0(X0,X1) != X2 ) )
      | ~ sP4(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X1,X0,X2] :
      ( ( k2_yellow_0(X0,X1) = X2
      <=> sP3(X2,X0,X1) )
      | ~ sP4(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f149,plain,(
    ! [X0] : sP4(sK7,sK5,k2_yellow_0(sK5,X0)) ),
    inference(subsumption_resolution,[],[f146,f77])).

fof(f77,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7)
      | ~ r2_yellow_0(sK6,sK7) )
    & r2_hidden(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
    & r2_yellow_0(sK5,sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_yellow_0(sK6,sK5)
    & v4_yellow_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_orders_2(sK5)
    & v4_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f20,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                  | ~ r2_yellow_0(X1,X2) )
                & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                & r2_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X1,X2) != k2_yellow_0(sK5,X2)
                | ~ r2_yellow_0(X1,X2) )
              & r2_hidden(k2_yellow_0(sK5,X2),u1_struct_0(X1))
              & r2_yellow_0(sK5,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK5)
          & v4_yellow_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK5)
      & v4_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_yellow_0(X1,X2) != k2_yellow_0(sK5,X2)
              | ~ r2_yellow_0(X1,X2) )
            & r2_hidden(k2_yellow_0(sK5,X2),u1_struct_0(X1))
            & r2_yellow_0(sK5,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_yellow_0(X1,sK5)
        & v4_yellow_0(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_yellow_0(sK5,X2) != k2_yellow_0(sK6,X2)
            | ~ r2_yellow_0(sK6,X2) )
          & r2_hidden(k2_yellow_0(sK5,X2),u1_struct_0(sK6))
          & r2_yellow_0(sK5,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
      & m1_yellow_0(sK6,sK5)
      & v4_yellow_0(sK6,sK5)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ( k2_yellow_0(sK5,X2) != k2_yellow_0(sK6,X2)
          | ~ r2_yellow_0(sK6,X2) )
        & r2_hidden(k2_yellow_0(sK5,X2),u1_struct_0(sK6))
        & r2_yellow_0(sK5,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ( k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7)
        | ~ r2_yellow_0(sK6,sK7) )
      & r2_hidden(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
      & r2_yellow_0(sK5,sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                    & r2_yellow_0(X0,X2) )
                 => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                    & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(f146,plain,(
    ! [X0] :
      ( sP4(sK7,sK5,k2_yellow_0(sK5,X0))
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f145,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
      | sP4(sK7,sK5,X0) ) ),
    inference(subsumption_resolution,[],[f144,f77])).

fof(f144,plain,(
    ! [X0] :
      ( sP4(sK7,sK5,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f113,f82])).

fof(f82,plain,(
    r2_yellow_0(sK5,sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | sP4(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X1,X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f30,f51,f50])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f3542,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | ~ r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f3440,f287])).

fof(f287,plain,(
    ! [X0] :
      ( r1_lattice3(sK6,X0,k2_yellow_0(sK5,sK7))
      | ~ r1_lattice3(sK5,X0,k2_yellow_0(sK5,sK7)) ) ),
    inference(resolution,[],[f286,f137])).

fof(f137,plain,(
    m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f122,f83])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ r1_lattice3(sK5,X0,X1)
      | r1_lattice3(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f285,f165])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f164,f75])).

fof(f75,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f163,f77])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f162,f78])).

fof(f78,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f117,f80])).

fof(f80,plain,(
    m1_yellow_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_yellow_0)).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f284,f75])).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f283,f77])).

fof(f283,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f282,f78])).

fof(f282,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f281,f80])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_yellow_0(sK6,sK5)
      | r1_lattice3(sK6,X0,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f131,f79])).

fof(f79,plain,(
    v4_yellow_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f131,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | r1_lattice3(X1,X2,X4)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X3 = X4
                   => ( ( r2_lattice3(X0,X2,X3)
                       => r2_lattice3(X1,X2,X4) )
                      & ( r1_lattice3(X0,X2,X3)
                       => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_yellow_0)).

fof(f3440,plain,
    ( ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f715,f3429])).

fof(f3429,plain,(
    ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f3428,f3393])).

fof(f3393,plain,(
    k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f84,f3392])).

fof(f3392,plain,(
    r2_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f3391,f139])).

fof(f139,plain,(
    l1_orders_2(sK6) ),
    inference(resolution,[],[f138,f80])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_yellow_0(X0,sK5)
      | l1_orders_2(X0) ) ),
    inference(resolution,[],[f86,f77])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f3391,plain,
    ( r2_yellow_0(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f3368,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r2_yellow_0(X1,X0)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f90,f105])).

fof(f105,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f28,f48,f47,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              & r1_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f47,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ? [X2] :
          ( sP0(X2,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X5,X2)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP1(X1,X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_0)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0)
      | ~ sP1(X1,X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP1(X1,X0) )
          & ( sP1(X1,X0)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f3368,plain,(
    sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f3367,f139])).

fof(f3367,plain,
    ( sP1(sK7,sK6)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f3366,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f3366,plain,
    ( ~ l1_struct_0(sK6)
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f3364,f78])).

fof(f3364,plain,
    ( sP1(sK7,sK6)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f3353,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f3353,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f3336,f3352])).

fof(f3352,plain,
    ( m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f3348,f152])).

fof(f3348,plain,
    ( m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | ~ r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f3342,f287])).

fof(f3342,plain,
    ( ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f3341,f137])).

fof(f3341,plain,
    ( sP1(sK7,sK6)
    | m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f3329,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ sP0(X2,X1,X0)
            | ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X2)
              & r1_lattice3(X1,X0,sK8(X0,X1,X2))
              & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ( sP0(sK9(X0,X1),X1,X0)
          & ! [X5] :
              ( r1_orders_2(X1,X5,sK9(X0,X1))
              | ~ r1_lattice3(X1,X0,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_lattice3(X1,X0,sK9(X0,X1))
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X2)
          & r1_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X2)
        & r1_lattice3(X1,X0,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X1,X0)
          & ! [X5] :
              ( r1_orders_2(X1,X5,X4)
              | ~ r1_lattice3(X1,X0,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_lattice3(X1,X0,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP0(sK9(X0,X1),X1,X0)
        & ! [X5] :
            ( r1_orders_2(X1,X5,sK9(X0,X1))
            | ~ r1_lattice3(X1,X0,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & r1_lattice3(X1,X0,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ sP0(X2,X1,X0)
            | ? [X3] :
                ( ~ r1_orders_2(X1,X3,X2)
                & r1_lattice3(X1,X0,X3)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP0(X4,X1,X0)
            & ! [X5] :
                ( r1_orders_2(X1,X5,X4)
                | ~ r1_lattice3(X1,X0,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & r1_lattice3(X1,X0,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ! [X2] :
            ( ~ sP0(X2,X0,X1)
            | ? [X5] :
                ( ~ r1_orders_2(X0,X5,X2)
                & r1_lattice3(X0,X1,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP0(X2,X0,X1)
            & ! [X5] :
                ( r1_orders_2(X0,X5,X2)
                | ~ r1_lattice3(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f3329,plain,(
    sP0(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(trivial_inequality_removal,[],[f3323])).

fof(f3323,plain,
    ( k2_yellow_0(sK5,sK7) != k2_yellow_0(sK5,sK7)
    | sP0(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(superposition,[],[f104,f3147])).

fof(f3147,plain,(
    k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f3146,f139])).

fof(f3146,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f3145,f85])).

fof(f3145,plain,
    ( ~ l1_struct_0(sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f3143,f78])).

fof(f3143,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f3142,f114])).

fof(f3142,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f3140,f152])).

fof(f3140,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f3036,f287])).

fof(f3036,plain,
    ( ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[],[f3033,f715])).

fof(f3033,plain,
    ( ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f3032,f2970])).

fof(f2970,plain,
    ( k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f2969,f84])).

fof(f2969,plain,
    ( r2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f2966,f139])).

fof(f2966,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | r2_yellow_0(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f2946,f141])).

fof(f2946,plain,
    ( sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f2945,f139])).

fof(f2945,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f2944,f85])).

fof(f2944,plain,
    ( ~ l1_struct_0(sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f2942,f78])).

fof(f2942,plain,
    ( sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f2933,f114])).

fof(f2933,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f2931,f530])).

fof(f530,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | k2_yellow_0(sK5,sK7) = sK10(X0,sK6,sK7) ) ),
    inference(duplicate_literal_removal,[],[f527])).

fof(f527,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP0(X0,sK6,sK7)
      | k2_yellow_0(sK5,sK7) = sK10(X0,sK6,sK7) ) ),
    inference(resolution,[],[f526,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ sP3(sK10(X0,sK6,X1),sK5,sK7)
      | sP0(X0,sK6,X1)
      | k2_yellow_0(sK5,sK7) = sK10(X0,sK6,X1) ) ),
    inference(resolution,[],[f177,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X2,X1,X0)
      | k2_yellow_0(X1,X0) = X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f177,plain,(
    ! [X0,X1] :
      ( sP4(sK7,sK5,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1) ) ),
    inference(resolution,[],[f169,f145])).

fof(f169,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK10(X2,sK6,X3),u1_struct_0(sK5))
      | sP0(X2,sK6,X3) ) ),
    inference(resolution,[],[f165,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK10(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,X4,sK10(X0,X1,X2))
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,sK10(X0,X1,X2))
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,sK11(X1,X2,X5),X5)
              & r1_lattice3(X1,X2,sK11(X1,X2,X5))
              & m1_subset_1(sK11(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f64,f66,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X4,X3)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK10(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,X4,sK10(X0,X1,X2))
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r1_lattice3(X1,X2,sK10(X0,X1,X2))
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X6,X5)
          & r1_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK11(X1,X2,X5),X5)
        & r1_lattice3(X1,X2,sK11(X1,X2,X5))
        & m1_subset_1(sK11(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X4,X3)
                | ~ r1_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X6,X5)
                & r1_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X4,X3)
                | ~ r1_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f526,plain,(
    ! [X0] :
      ( sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | sP0(X0,sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f525,f256])).

fof(f256,plain,(
    ! [X1] :
      ( r1_lattice3(sK5,sK7,sK10(X1,sK6,sK7))
      | sP0(X1,sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f251,f101])).

fof(f251,plain,(
    ! [X1] :
      ( r1_lattice3(sK5,sK7,sK10(X1,sK6,sK7))
      | ~ m1_subset_1(sK10(X1,sK6,sK7),u1_struct_0(sK6))
      | sP0(X1,sK6,sK7) ) ),
    inference(resolution,[],[f248,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK10(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f248,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK6,sK7,X0)
      | r1_lattice3(sK5,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f247,f75])).

fof(f247,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_lattice3(sK5,sK7,X0)
      | ~ r1_lattice3(sK6,sK7,X0)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f246,f77])).

fof(f246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_lattice3(sK5,sK7,X0)
      | ~ r1_lattice3(sK6,sK7,X0)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f245,f80])).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(sK6,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_lattice3(X1,sK7,X0)
      | ~ r1_lattice3(sK6,sK7,X0)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f244,f78])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK6,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_lattice3(X1,sK7,X0)
      | ~ m1_yellow_0(sK6,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f135,f81])).

fof(f81,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f56])).

fof(f135,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattice3(X0,X2,X4)
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f133,f117])).

fof(f133,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattice3(X0,X2,X4)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X1,X2,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_yellow_0)).

fof(f525,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r1_lattice3(sK5,sK7,sK10(X0,sK6,sK7)) ) ),
    inference(duplicate_literal_removal,[],[f524])).

fof(f524,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r1_lattice3(sK5,sK7,sK10(X0,sK6,sK7))
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r1_lattice3(sK5,sK7,sK10(X0,sK6,sK7)) ) ),
    inference(resolution,[],[f362,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK12(X0,X1,X2))
      | sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f362,plain,(
    ! [X10,X9] :
      ( ~ r1_lattice3(sK5,sK7,sK12(sK10(X9,sK6,sK7),sK5,X10))
      | sP0(X9,sK6,sK7)
      | sP3(sK10(X9,sK6,sK7),sK5,X10)
      | ~ r1_lattice3(sK5,X10,sK10(X9,sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f354,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f354,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(sK12(sK10(X9,sK6,sK7),sK5,X10),u1_struct_0(sK5))
      | sP0(X9,sK6,sK7)
      | ~ r1_lattice3(sK5,sK7,sK12(sK10(X9,sK6,sK7),sK5,X10))
      | sP3(sK10(X9,sK6,sK7),sK5,X10)
      | ~ r1_lattice3(sK5,X10,sK10(X9,sK6,sK7)) ) ),
    inference(resolution,[],[f350,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK12(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f350,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK5,X1,sK10(X0,sK6,sK7))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | sP0(X0,sK6,sK7)
      | ~ r1_lattice3(sK5,sK7,X1) ) ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,(
    ! [X0,X1] :
      ( sP0(X0,sK6,sK7)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_orders_2(sK5,X1,sK10(X0,sK6,sK7))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,X1) ) ),
    inference(resolution,[],[f337,f158])).

fof(f158,plain,(
    ! [X0] :
      ( r1_orders_2(sK5,X0,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,X0) ) ),
    inference(resolution,[],[f109,f150])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f337,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK5,X5,k2_yellow_0(sK5,sK7))
      | sP0(X4,sK6,sK7)
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | r1_orders_2(sK5,X5,sK10(X4,sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f336,f169])).

fof(f336,plain,(
    ! [X4,X5] :
      ( sP0(X4,sK6,sK7)
      | ~ r1_orders_2(sK5,X5,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(sK10(X4,sK6,sK7),u1_struct_0(sK5))
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | r1_orders_2(sK5,X5,sK10(X4,sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f330,f166])).

fof(f166,plain,(
    m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK5)) ),
    inference(resolution,[],[f165,f137])).

fof(f330,plain,(
    ! [X4,X5] :
      ( sP0(X4,sK6,sK7)
      | ~ r1_orders_2(sK5,X5,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(sK10(X4,sK6,sK7),u1_struct_0(sK5))
      | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK5))
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | r1_orders_2(sK5,X5,sK10(X4,sK6,sK7)) ) ),
    inference(resolution,[],[f327,f260])).

fof(f260,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK5,X0,X1)
      | ~ r1_orders_2(sK5,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | r1_orders_2(sK5,X2,X1) ) ),
    inference(subsumption_resolution,[],[f259,f77])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK5,X0,X1)
      | ~ r1_orders_2(sK5,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5)
      | r1_orders_2(sK5,X2,X1) ) ),
    inference(resolution,[],[f120,f76])).

fof(f76,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f327,plain,(
    ! [X0] :
      ( r1_orders_2(sK5,k2_yellow_0(sK5,sK7),sK10(X0,sK6,sK7))
      | sP0(X0,sK6,sK7) ) ),
    inference(resolution,[],[f326,f152])).

fof(f326,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X1,k2_yellow_0(sK5,sK7))
      | r1_orders_2(sK5,k2_yellow_0(sK5,sK7),sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1) ) ),
    inference(resolution,[],[f320,f287])).

fof(f320,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK6,X1,k2_yellow_0(sK5,sK7))
      | sP0(X0,sK6,X1)
      | r1_orders_2(sK5,k2_yellow_0(sK5,sK7),sK10(X0,sK6,X1)) ) ),
    inference(resolution,[],[f319,f137])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK5,X2,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1)
      | ~ r1_lattice3(sK6,X1,X2) ) ),
    inference(subsumption_resolution,[],[f318,f101])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK10(X0,sK6,X1),u1_struct_0(sK6))
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK5,X2,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1)
      | ~ r1_lattice3(sK6,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK10(X0,sK6,X1),u1_struct_0(sK6))
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK5,X2,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1)
      | ~ r1_lattice3(sK6,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f313,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X1,X4,sK10(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f312,f165])).

fof(f312,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f311,f165])).

fof(f311,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f310,f77])).

fof(f310,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f126,f80])).

fof(f126,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

fof(f2931,plain,
    ( ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(duplicate_literal_removal,[],[f2918])).

fof(f2918,plain,
    ( ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f2916,f595])).

fof(f595,plain,
    ( m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f594,f152])).

fof(f594,plain,
    ( m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f543,f287])).

fof(f543,plain,
    ( ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f533,f137])).

fof(f533,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK6))
      | sP1(sK7,sK6)
      | m1_subset_1(sK8(sK7,sK6,X4),u1_struct_0(sK6))
      | ~ r1_lattice3(sK6,sK7,X4)
      | k2_yellow_0(sK5,sK7) = sK10(X4,sK6,sK7) ) ),
    inference(resolution,[],[f530,f95])).

fof(f2916,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f2914,f152])).

fof(f2914,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f2912,f287])).

fof(f2912,plain,
    ( ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f2911,f137])).

fof(f2911,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(duplicate_literal_removal,[],[f2910])).

fof(f2910,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f729,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X0,sK8(X0,X1,X2))
      | ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f729,plain,(
    ! [X2] :
      ( ~ r1_lattice3(sK6,sK7,sK8(X2,sK6,k2_yellow_0(sK5,sK7)))
      | ~ m1_subset_1(sK8(X2,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ sP0(k2_yellow_0(sK5,sK7),sK6,X2)
      | sP1(X2,sK6)
      | ~ r1_lattice3(sK6,X2,k2_yellow_0(sK5,sK7)) ) ),
    inference(subsumption_resolution,[],[f724,f137])).

fof(f724,plain,(
    ! [X2] :
      ( ~ r1_lattice3(sK6,sK7,sK8(X2,sK6,k2_yellow_0(sK5,sK7)))
      | ~ m1_subset_1(sK8(X2,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ sP0(k2_yellow_0(sK5,sK7),sK6,X2)
      | sP1(X2,sK6)
      | ~ r1_lattice3(sK6,X2,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f721,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X2)
      | ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f721,plain,(
    ! [X2] :
      ( r1_orders_2(sK6,X2,k2_yellow_0(sK5,sK7))
      | ~ r1_lattice3(sK6,sK7,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | v1_xboole_0(u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f719,f152])).

fof(f719,plain,(
    ! [X2] :
      ( v1_xboole_0(u1_struct_0(sK6))
      | ~ r1_lattice3(sK6,sK7,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK6,X2,k2_yellow_0(sK5,sK7))
      | ~ r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ) ),
    inference(resolution,[],[f716,f287])).

fof(f716,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ r1_lattice3(sK6,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_orders_2(sK6,X0,k2_yellow_0(sK5,sK7)) ) ),
    inference(resolution,[],[f715,f109])).

fof(f3032,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | k2_yellow_0(sK5,sK7) = k2_yellow_0(sK6,sK7) ),
    inference(resolution,[],[f2992,f107])).

fof(f2992,plain,
    ( sP4(sK7,sK6,k2_yellow_0(sK5,sK7))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f2989,f137])).

fof(f2989,plain,(
    ! [X18] :
      ( ~ m1_subset_1(X18,u1_struct_0(sK6))
      | sP4(sK7,sK6,X18)
      | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f2988,f139])).

fof(f2988,plain,(
    ! [X18] :
      ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
      | sP4(sK7,sK6,X18)
      | ~ m1_subset_1(X18,u1_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(resolution,[],[f2969,f113])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sK10(X0,X1,X2) != X0
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f3336,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(global_subsumption,[],[f2916,f3329])).

fof(f84,plain,
    ( ~ r2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f3428,plain,
    ( ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | k2_yellow_0(sK5,sK7) = k2_yellow_0(sK6,sK7) ),
    inference(resolution,[],[f3415,f107])).

fof(f3415,plain,(
    sP4(sK7,sK6,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f3414,f137])).

fof(f3414,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK6))
      | sP4(sK7,sK6,X6) ) ),
    inference(subsumption_resolution,[],[f3413,f139])).

fof(f3413,plain,(
    ! [X6] :
      ( sP4(sK7,sK6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(resolution,[],[f3392,f113])).

fof(f715,plain,
    ( sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(duplicate_literal_removal,[],[f714])).

fof(f714,plain,
    ( sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | v1_xboole_0(u1_struct_0(sK6))
    | sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f674,f258])).

fof(f258,plain,(
    ! [X3] :
      ( r1_lattice3(sK5,sK7,sK12(X3,sK6,sK7))
      | sP3(X3,sK6,sK7)
      | ~ r1_lattice3(sK6,sK7,X3) ) ),
    inference(subsumption_resolution,[],[f253,f110])).

fof(f253,plain,(
    ! [X3] :
      ( r1_lattice3(sK5,sK7,sK12(X3,sK6,sK7))
      | ~ m1_subset_1(sK12(X3,sK6,sK7),u1_struct_0(sK6))
      | sP3(X3,sK6,sK7)
      | ~ r1_lattice3(sK6,sK7,X3) ) ),
    inference(resolution,[],[f248,f111])).

fof(f674,plain,(
    ! [X3] :
      ( ~ r1_lattice3(sK5,sK7,sK12(k2_yellow_0(sK5,sK7),sK6,X3))
      | sP3(k2_yellow_0(sK5,sK7),sK6,X3)
      | ~ r1_lattice3(sK6,X3,k2_yellow_0(sK5,sK7))
      | v1_xboole_0(u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f673,f170])).

fof(f170,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK12(X4,sK6,X5),u1_struct_0(sK5))
      | sP3(X4,sK6,X5)
      | ~ r1_lattice3(sK6,X5,X4) ) ),
    inference(resolution,[],[f165,f110])).

fof(f673,plain,(
    ! [X3] :
      ( v1_xboole_0(u1_struct_0(sK6))
      | sP3(k2_yellow_0(sK5,sK7),sK6,X3)
      | ~ r1_lattice3(sK6,X3,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(sK12(k2_yellow_0(sK5,sK7),sK6,X3),u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,sK12(k2_yellow_0(sK5,sK7),sK6,X3)) ) ),
    inference(subsumption_resolution,[],[f667,f137])).

fof(f667,plain,(
    ! [X3] :
      ( v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
      | sP3(k2_yellow_0(sK5,sK7),sK6,X3)
      | ~ r1_lattice3(sK6,X3,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(sK12(k2_yellow_0(sK5,sK7),sK6,X3),u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,sK12(k2_yellow_0(sK5,sK7),sK6,X3)) ) ),
    inference(resolution,[],[f663,f158])).

fof(f663,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK5,sK12(X3,sK6,X4),X3)
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(X3,u1_struct_0(sK6))
      | sP3(X3,sK6,X4)
      | ~ r1_lattice3(sK6,X4,X3) ) ),
    inference(duplicate_literal_removal,[],[f662])).

fof(f662,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK6))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,sK12(X3,sK6,X4),X3)
      | sP3(X3,sK6,X4)
      | ~ r1_lattice3(sK6,X4,X3)
      | sP3(X3,sK6,X4)
      | ~ r1_lattice3(sK6,X4,X3) ) ),
    inference(resolution,[],[f433,f112])).

fof(f433,plain,(
    ! [X10,X8,X9] :
      ( r1_orders_2(sK6,sK12(X9,sK6,X10),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK6))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,sK12(X9,sK6,X10),X8)
      | sP3(X9,sK6,X10)
      | ~ r1_lattice3(sK6,X10,X9) ) ),
    inference(resolution,[],[f426,f110])).

fof(f426,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK6,X1,X2)
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X1,X2) ) ),
    inference(subsumption_resolution,[],[f424,f165])).

fof(f424,plain,(
    ! [X2,X1] :
      ( ~ r1_orders_2(sK5,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_orders_2(sK6,X1,X2)
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f415,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f415,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f414,f165])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f413,f77])).

fof(f413,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(subsumption_resolution,[],[f412,f80])).

fof(f412,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_yellow_0(sK6,sK5)
      | r1_orders_2(sK6,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f136,f79])).

fof(f136,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f128,f122])).

fof(f128,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

fof(f83,plain,(
    r2_hidden(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f56])).

%------------------------------------------------------------------------------
