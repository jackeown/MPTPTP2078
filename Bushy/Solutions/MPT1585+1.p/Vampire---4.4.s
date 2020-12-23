%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t64_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 23.00s
% Output     : Refutation 23.00s
% Verified   : 
% Statistics : Number of formulae       :  277 (80474 expanded)
%              Number of leaves         :   29 (28787 expanded)
%              Depth                    :   87
%              Number of atoms          : 1434 (761248 expanded)
%              Number of equality atoms :  141 (73880 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35048,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f35045])).

fof(f35045,plain,(
    ! [X3] : ~ r2_hidden(X3,u1_struct_0(sK6)) ),
    inference(resolution,[],[f34957,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t7_boole)).

fof(f34957,plain,(
    v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f963,f34950])).

fof(f34950,plain,(
    ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f34949,f34771])).

fof(f34771,plain,(
    k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f114,f34770])).

fof(f34770,plain,(
    r2_yellow_0(sK6,sK7) ),
    inference(subsumption_resolution,[],[f34767,f180])).

fof(f180,plain,(
    l1_orders_2(sK6) ),
    inference(resolution,[],[f178,f110])).

fof(f110,plain,(
    m1_yellow_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f77,f76,f75])).

fof(f75,plain,
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
              ( ( k2_yellow_0(sK5,X2) != k2_yellow_0(X1,X2)
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

fof(f76,plain,(
    ! [X0] :
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
     => ( ? [X2] :
            ( ( k2_yellow_0(sK6,X2) != k2_yellow_0(X0,X2)
              | ~ r2_yellow_0(sK6,X2) )
            & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(sK6))
            & r2_yellow_0(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & m1_yellow_0(sK6,X0)
        & v4_yellow_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
            | ~ r2_yellow_0(X1,X2) )
          & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
          & r2_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( k2_yellow_0(X0,sK7) != k2_yellow_0(X1,sK7)
          | ~ r2_yellow_0(X1,sK7) )
        & r2_hidden(k2_yellow_0(X0,sK7),u1_struct_0(X1))
        & r2_yellow_0(X0,sK7)
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t64_yellow_0)).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_yellow_0(X0,sK5)
      | l1_orders_2(X0) ) ),
    inference(resolution,[],[f117,f107])).

fof(f107,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',dt_m1_yellow_0)).

fof(f34767,plain,
    ( r2_yellow_0(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f34681,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r2_yellow_0(X1,X0)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f121,f136])).

fof(f136,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f44,f70,f69,f68])).

fof(f68,plain,(
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

fof(f69,plain,(
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

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP1(X1,X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',d8_yellow_0)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0)
      | ~ sP1(X1,X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP1(X1,X0) )
          & ( sP1(X1,X0)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f34681,plain,(
    sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f34680,f180])).

fof(f34680,plain,
    ( sP1(sK7,sK6)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f34679,f116])).

fof(f116,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',dt_l1_orders_2)).

fof(f34679,plain,
    ( ~ l1_struct_0(sK6)
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f34674,f108])).

fof(f108,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f78])).

fof(f34674,plain,
    ( sP1(sK7,sK6)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f34630,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',fc2_struct_0)).

fof(f34630,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f34629,f177])).

fof(f177,plain,(
    m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f156,f113])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t1_subset)).

fof(f34629,plain,
    ( sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f34628,f736])).

fof(f736,plain,(
    r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(subsumption_resolution,[],[f726,f177])).

fof(f726,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
    | r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f725,f287])).

fof(f287,plain,(
    r1_lattice3(sK5,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f285,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f94,f95])).

fof(f95,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK12(X0,X1,X2),X0)
        & r1_lattice3(X1,X2,sK12(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
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
    inference(rectify,[],[f93])).

fof(f93,plain,(
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
    inference(flattening,[],[f92])).

fof(f92,plain,(
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
    inference(nnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f285,plain,(
    sP3(k2_yellow_0(sK5,sK7),sK5,sK7) ),
    inference(resolution,[],[f283,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1,k2_yellow_0(X1,X0))
      | sP3(k2_yellow_0(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k2_yellow_0(X1,X0) != X2
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_yellow_0(X1,X0) = X2
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | k2_yellow_0(X1,X0) != X2 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f90])).

fof(f90,plain,(
    ! [X1,X0,X2] :
      ( ( ( k2_yellow_0(X0,X1) = X2
          | ~ sP3(X2,X0,X1) )
        & ( sP3(X2,X0,X1)
          | k2_yellow_0(X0,X1) != X2 ) )
      | ~ sP4(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X1,X0,X2] :
      ( ( k2_yellow_0(X0,X1) = X2
      <=> sP3(X2,X0,X1) )
      | ~ sP4(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f283,plain,(
    ! [X0] : sP4(sK7,sK5,k2_yellow_0(sK5,X0)) ),
    inference(subsumption_resolution,[],[f278,f107])).

fof(f278,plain,(
    ! [X0] :
      ( sP4(sK7,sK5,k2_yellow_0(sK5,X0))
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f277,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',dt_k2_yellow_0)).

fof(f277,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
      | sP4(sK7,sK5,X0) ) ),
    inference(subsumption_resolution,[],[f276,f107])).

fof(f276,plain,(
    ! [X0] :
      ( sP4(sK7,sK5,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f144,f112])).

fof(f112,plain,(
    r2_yellow_0(sK5,sK7) ),
    inference(cnf_transformation,[],[f78])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | sP4(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X1,X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f46,f73,f72])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',d10_yellow_0)).

fof(f725,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | r1_lattice3(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f724,f346])).

fof(f346,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f345,f105])).

fof(f105,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f345,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f344,f107])).

fof(f344,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f341,f108])).

fof(f341,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | m1_subset_1(X0,u1_struct_0(sK5))
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f149,f110])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t59_yellow_0)).

fof(f724,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f723,f105])).

fof(f723,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f722,f107])).

fof(f722,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f721,f108])).

fof(f721,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_lattice3(sK6,X0,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f720,f110])).

fof(f720,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_yellow_0(sK6,sK5)
      | r1_lattice3(sK6,X0,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f170,f109])).

fof(f109,plain,(
    v4_yellow_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f170,plain,(
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
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t62_yellow_0)).

fof(f34628,plain,
    ( sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f34626,f34500])).

fof(f34500,plain,(
    sP0(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(trivial_inequality_removal,[],[f34493])).

fof(f34493,plain,
    ( k2_yellow_0(sK5,sK7) != k2_yellow_0(sK5,sK7)
    | sP0(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(superposition,[],[f135,f34338])).

fof(f34338,plain,(
    k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f34337,f180])).

fof(f34337,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f34336,f116])).

fof(f34336,plain,
    ( ~ l1_struct_0(sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f34331,f108])).

fof(f34331,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f34328,f146])).

fof(f34328,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f34324,f963])).

fof(f34324,plain,
    ( ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f34323,f34062])).

fof(f34062,plain,
    ( k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f34061,f114])).

fof(f34061,plain,
    ( r2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f34057,f180])).

fof(f34057,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | r2_yellow_0(sK6,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f33990,f209])).

fof(f33990,plain,
    ( sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f33989,f180])).

fof(f33989,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[],[f33988,f116])).

fof(f33988,plain,
    ( ~ l1_struct_0(sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f33983,f108])).

fof(f33983,plain,
    ( sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f33982,f146])).

fof(f33982,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f33981,f177])).

fof(f33981,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f33970,f736])).

fof(f33970,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(duplicate_literal_removal,[],[f33969])).

fof(f33969,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(condensation,[],[f33968])).

fof(f33968,plain,(
    ! [X3] :
      ( sP1(sK7,sK6)
      | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
      | v1_xboole_0(u1_struct_0(sK6))
      | k2_yellow_0(sK5,sK7) = sK10(X3,sK6,sK7)
      | sK10(k2_yellow_0(sK5,sK7),sK6,sK7) = X3
      | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ) ),
    inference(duplicate_literal_removal,[],[f33964])).

fof(f33964,plain,(
    ! [X3] :
      ( sP1(sK7,sK6)
      | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
      | v1_xboole_0(u1_struct_0(sK6))
      | k2_yellow_0(sK5,sK7) = sK10(X3,sK6,sK7)
      | sP1(sK7,sK6)
      | sK10(k2_yellow_0(sK5,sK7),sK6,sK7) = X3
      | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f33957,f1622])).

fof(f1622,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK8(sK7,sK6,X15),u1_struct_0(sK6))
      | k2_yellow_0(sK5,sK7) = sK10(X16,sK6,sK7)
      | sP1(sK7,sK6)
      | sK10(X15,sK6,sK7) = X16
      | ~ r1_lattice3(sK6,sK7,X15)
      | ~ m1_subset_1(X15,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f1616,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f81,f83,f82])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X2)
          & r1_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK8(X0,X1,X2),X2)
        & r1_lattice3(X1,X0,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
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

fof(f81,plain,(
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
    inference(rectify,[],[f80])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f69])).

fof(f1616,plain,(
    ! [X0,X1] :
      ( sP0(X0,sK6,sK7)
      | sK10(X0,sK6,sK7) = X1
      | k2_yellow_0(sK5,sK7) = sK10(X1,sK6,sK7) ) ),
    inference(duplicate_literal_removal,[],[f1615])).

fof(f1615,plain,(
    ! [X0,X1] :
      ( sK10(X0,sK6,sK7) = X1
      | sP0(X0,sK6,sK7)
      | k2_yellow_0(sK5,sK7) = sK10(X1,sK6,sK7)
      | k2_yellow_0(sK5,sK7) = sK10(X1,sK6,sK7) ) ),
    inference(condensation,[],[f1604])).

fof(f1604,plain,(
    ! [X4,X2,X3] :
      ( sP0(X2,sK6,sK7)
      | sK10(X2,sK6,sK7) = X3
      | k2_yellow_0(sK5,sK7) = sK10(X4,sK6,sK7)
      | sK10(X2,sK6,sK7) = X4
      | k2_yellow_0(sK5,sK7) = sK10(X3,sK6,sK7) ) ),
    inference(resolution,[],[f1590,f1293])).

fof(f1293,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | k2_yellow_0(sK5,sK7) = sK10(X0,sK6,sK7) ) ),
    inference(duplicate_literal_removal,[],[f1290])).

fof(f1290,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP0(X0,sK6,sK7)
      | k2_yellow_0(sK5,sK7) = sK10(X0,sK6,sK7) ) ),
    inference(resolution,[],[f1289,f373])).

fof(f373,plain,(
    ! [X0,X1] :
      ( ~ sP3(sK10(X0,sK6,X1),sK5,sK7)
      | sP0(X0,sK6,X1)
      | k2_yellow_0(sK5,sK7) = sK10(X0,sK6,X1) ) ),
    inference(resolution,[],[f371,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X2,X1,X0)
      | k2_yellow_0(X1,X0) = X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f371,plain,(
    ! [X0,X1] :
      ( sP4(sK7,sK5,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1) ) ),
    inference(resolution,[],[f351,f277])).

fof(f351,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK10(X3,sK6,X4),u1_struct_0(sK5))
      | sP0(X3,sK6,X4) ) ),
    inference(resolution,[],[f346,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f86,f88,f87])).

fof(f87,plain,(
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

fof(f88,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X6,X5)
          & r1_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK11(X1,X2,X5),X5)
        & r1_lattice3(X1,X2,sK11(X1,X2,X5))
        & m1_subset_1(sK11(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
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
    inference(rectify,[],[f85])).

fof(f85,plain,(
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
    inference(nnf_transformation,[],[f68])).

fof(f1289,plain,(
    ! [X0] :
      ( sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | sP0(X0,sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f1288,f111])).

fof(f111,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f78])).

fof(f1288,plain,(
    ! [X0] :
      ( sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | sP0(X0,sK6,sK7)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(duplicate_literal_removal,[],[f1287])).

fof(f1287,plain,(
    ! [X0] :
      ( sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | sP0(X0,sK6,sK7)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP0(X0,sK6,sK7) ) ),
    inference(resolution,[],[f1286,f625])).

fof(f625,plain,(
    ! [X4,X3] :
      ( r1_lattice3(sK5,X4,sK10(X3,sK6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP0(X3,sK6,X4) ) ),
    inference(subsumption_resolution,[],[f621,f132])).

fof(f621,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK10(X3,sK6,X4),u1_struct_0(sK6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
      | r1_lattice3(sK5,X4,sK10(X3,sK6,X4))
      | sP0(X3,sK6,X4) ) ),
    inference(resolution,[],[f618,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK10(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f618,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
      | r1_lattice3(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f617,f105])).

fof(f617,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
      | r1_lattice3(sK5,X0,X1)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f616,f107])).

fof(f616,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
      | r1_lattice3(sK5,X0,X1)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f613,f108])).

fof(f613,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
      | r1_lattice3(sK5,X0,X1)
      | v2_struct_0(sK6)
      | ~ l1_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f174,f110])).

fof(f174,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_lattice3(X0,X2,X4)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f172,f149])).

fof(f172,plain,(
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
    inference(equality_resolution,[],[f150])).

fof(f150,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t63_yellow_0)).

fof(f1286,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK5,sK7,sK10(X0,sK6,sK7))
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | sP0(X0,sK6,sK7) ) ),
    inference(duplicate_literal_removal,[],[f1285])).

fof(f1285,plain,(
    ! [X0] :
      ( sP0(X0,sK6,sK7)
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r1_lattice3(sK5,sK7,sK10(X0,sK6,sK7))
      | sP3(sK10(X0,sK6,sK7),sK5,sK7)
      | ~ r1_lattice3(sK5,sK7,sK10(X0,sK6,sK7)) ) ),
    inference(resolution,[],[f1183,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK12(X0,X1,X2))
      | sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f1183,plain,(
    ! [X17,X16] :
      ( ~ r1_lattice3(sK5,sK7,sK12(sK10(X16,sK6,sK7),sK5,X17))
      | sP0(X16,sK6,sK7)
      | sP3(sK10(X16,sK6,sK7),sK5,X17)
      | ~ r1_lattice3(sK5,X17,sK10(X16,sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f1172,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f1172,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(sK12(sK10(X16,sK6,sK7),sK5,X17),u1_struct_0(sK5))
      | sP0(X16,sK6,sK7)
      | ~ r1_lattice3(sK5,sK7,sK12(sK10(X16,sK6,sK7),sK5,X17))
      | sP3(sK10(X16,sK6,sK7),sK5,X17)
      | ~ r1_lattice3(sK5,X17,sK10(X16,sK6,sK7)) ) ),
    inference(resolution,[],[f1132,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK12(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f1132,plain,(
    ! [X4,X5] :
      ( r1_orders_2(sK5,X5,sK10(X4,sK6,sK7))
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | sP0(X4,sK6,sK7)
      | ~ r1_lattice3(sK5,sK7,X5) ) ),
    inference(duplicate_literal_removal,[],[f1125])).

fof(f1125,plain,(
    ! [X4,X5] :
      ( sP0(X4,sK6,sK7)
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | r1_orders_2(sK5,X5,sK10(X4,sK6,sK7))
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,X5) ) ),
    inference(resolution,[],[f1116,f328])).

fof(f328,plain,(
    ! [X0] :
      ( r1_orders_2(sK5,X0,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,X0) ) ),
    inference(resolution,[],[f140,f285])).

fof(f140,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f1116,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK5,X1,k2_yellow_0(sK5,sK7))
      | sP0(X0,sK6,sK7)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_orders_2(sK5,X1,sK10(X0,sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f1108,f177])).

fof(f1108,plain,(
    ! [X0,X1] :
      ( sP0(X0,sK6,sK7)
      | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X1,k2_yellow_0(sK5,sK7))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_orders_2(sK5,X1,sK10(X0,sK6,sK7)) ) ),
    inference(resolution,[],[f790,f736])).

fof(f790,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_lattice3(sK6,X10,X8)
      | sP0(X9,sK6,X10)
      | ~ m1_subset_1(X8,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X11,X8)
      | ~ m1_subset_1(X11,u1_struct_0(sK5))
      | r1_orders_2(sK5,X11,sK10(X9,sK6,X10)) ) ),
    inference(subsumption_resolution,[],[f789,f351])).

fof(f789,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK6))
      | sP0(X9,sK6,X10)
      | ~ r1_lattice3(sK6,X10,X8)
      | ~ r1_orders_2(sK5,X11,X8)
      | ~ m1_subset_1(sK10(X9,sK6,X10),u1_struct_0(sK5))
      | ~ m1_subset_1(X11,u1_struct_0(sK5))
      | r1_orders_2(sK5,X11,sK10(X9,sK6,X10)) ) ),
    inference(subsumption_resolution,[],[f782,f346])).

fof(f782,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK6))
      | sP0(X9,sK6,X10)
      | ~ r1_lattice3(sK6,X10,X8)
      | ~ r1_orders_2(sK5,X11,X8)
      | ~ m1_subset_1(sK10(X9,sK6,X10),u1_struct_0(sK5))
      | ~ m1_subset_1(X8,u1_struct_0(sK5))
      | ~ m1_subset_1(X11,u1_struct_0(sK5))
      | r1_orders_2(sK5,X11,sK10(X9,sK6,X10)) ) ),
    inference(resolution,[],[f779,f646])).

fof(f646,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK5,X0,X1)
      | ~ r1_orders_2(sK5,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | r1_orders_2(sK5,X2,X1) ) ),
    inference(subsumption_resolution,[],[f645,f107])).

fof(f645,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK5,X0,X1)
      | ~ r1_orders_2(sK5,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5)
      | r1_orders_2(sK5,X2,X1) ) ),
    inference(resolution,[],[f152,f106])).

fof(f106,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t26_orders_2)).

fof(f779,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK5,X2,sK10(X0,sK6,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | sP0(X0,sK6,X1)
      | ~ r1_lattice3(sK6,X1,X2) ) ),
    inference(subsumption_resolution,[],[f778,f132])).

fof(f778,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK10(X0,sK6,X1),u1_struct_0(sK6))
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK5,X2,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1)
      | ~ r1_lattice3(sK6,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f777])).

fof(f777,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK10(X0,sK6,X1),u1_struct_0(sK6))
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK5,X2,sK10(X0,sK6,X1))
      | sP0(X0,sK6,X1)
      | ~ r1_lattice3(sK6,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f776,f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X1,X4,sK10(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f776,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f775,f346])).

fof(f775,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f774,f346])).

fof(f774,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1) ) ),
    inference(subsumption_resolution,[],[f771,f107])).

fof(f771,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK6,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK5,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f165,f110])).

fof(f165,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f164])).

fof(f164,plain,(
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
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t60_yellow_0)).

fof(f1590,plain,(
    ! [X6,X7,X5] :
      ( ~ sP0(X5,sK6,sK7)
      | sP0(X6,sK6,sK7)
      | sK10(X6,sK6,sK7) = X5
      | k2_yellow_0(sK5,sK7) = sK10(X7,sK6,sK7)
      | sK10(X6,sK6,sK7) = X7 ) ),
    inference(subsumption_resolution,[],[f1589,f132])).

fof(f1589,plain,(
    ! [X6,X7,X5] :
      ( ~ sP0(X5,sK6,sK7)
      | sP0(X6,sK6,sK7)
      | sK10(X6,sK6,sK7) = X5
      | k2_yellow_0(sK5,sK7) = sK10(X7,sK6,sK7)
      | ~ m1_subset_1(sK10(X6,sK6,sK7),u1_struct_0(sK6))
      | sK10(X6,sK6,sK7) = X7 ) ),
    inference(subsumption_resolution,[],[f1588,f133])).

fof(f1588,plain,(
    ! [X6,X7,X5] :
      ( ~ sP0(X5,sK6,sK7)
      | sP0(X6,sK6,sK7)
      | sK10(X6,sK6,sK7) = X5
      | k2_yellow_0(sK5,sK7) = sK10(X7,sK6,sK7)
      | ~ r1_lattice3(sK6,sK7,sK10(X6,sK6,sK7))
      | ~ m1_subset_1(sK10(X6,sK6,sK7),u1_struct_0(sK6))
      | sK10(X6,sK6,sK7) = X7 ) ),
    inference(subsumption_resolution,[],[f1583,f1302])).

fof(f1302,plain,(
    ! [X2,X3] :
      ( ~ r1_lattice3(sK6,sK7,X3)
      | r1_lattice3(sK6,sK7,sK11(sK6,sK7,X3))
      | k2_yellow_0(sK5,sK7) = sK10(X2,sK6,sK7)
      | ~ m1_subset_1(X3,u1_struct_0(sK6))
      | X2 = X3 ) ),
    inference(resolution,[],[f1293,f130])).

fof(f130,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_lattice3(X1,X2,sK11(X1,X2,X5))
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f1583,plain,(
    ! [X6,X7,X5] :
      ( ~ sP0(X5,sK6,sK7)
      | sP0(X6,sK6,sK7)
      | ~ r1_lattice3(sK6,sK7,sK11(sK6,sK7,sK10(X6,sK6,sK7)))
      | sK10(X6,sK6,sK7) = X5
      | k2_yellow_0(sK5,sK7) = sK10(X7,sK6,sK7)
      | ~ r1_lattice3(sK6,sK7,sK10(X6,sK6,sK7))
      | ~ m1_subset_1(sK10(X6,sK6,sK7),u1_struct_0(sK6))
      | sK10(X6,sK6,sK7) = X7 ) ),
    inference(resolution,[],[f1264,f1303])).

fof(f1303,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK11(sK6,sK7,X5),u1_struct_0(sK6))
      | k2_yellow_0(sK5,sK7) = sK10(X4,sK6,sK7)
      | ~ r1_lattice3(sK6,sK7,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK6))
      | X4 = X5 ) ),
    inference(resolution,[],[f1293,f129])).

fof(f129,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK11(X1,X2,X5),u1_struct_0(X1))
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f89])).

fof(f1264,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK11(X1,X2,sK10(X0,X1,X2)),u1_struct_0(X1))
      | ~ sP0(X3,X1,X2)
      | sP0(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,sK11(X1,X2,sK10(X0,X1,X2)))
      | sK10(X0,X1,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f1263])).

fof(f1263,plain,(
    ! [X2,X0,X3,X1] :
      ( sK10(X0,X1,X2) = X3
      | ~ sP0(X3,X1,X2)
      | sP0(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,sK11(X1,X2,sK10(X0,X1,X2)))
      | ~ m1_subset_1(sK11(X1,X2,sK10(X0,X1,X2)),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f568,f133])).

fof(f568,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ r1_lattice3(X4,X6,sK10(X3,X4,X5))
      | sK10(X3,X4,X5) = X2
      | ~ sP0(X2,X4,X6)
      | sP0(X3,X4,X5)
      | ~ r1_lattice3(X4,X5,sK11(X4,X6,sK10(X3,X4,X5)))
      | ~ m1_subset_1(sK11(X4,X6,sK10(X3,X4,X5)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f566,f132])).

fof(f566,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( sK10(X3,X4,X5) = X2
      | ~ r1_lattice3(X4,X6,sK10(X3,X4,X5))
      | ~ m1_subset_1(sK10(X3,X4,X5),u1_struct_0(X4))
      | ~ sP0(X2,X4,X6)
      | sP0(X3,X4,X5)
      | ~ r1_lattice3(X4,X5,sK11(X4,X6,sK10(X3,X4,X5)))
      | ~ m1_subset_1(sK11(X4,X6,sK10(X3,X4,X5)),u1_struct_0(X4)) ) ),
    inference(resolution,[],[f131,f134])).

fof(f131,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r1_orders_2(X1,sK11(X1,X2,X5),X5)
      | X0 = X5
      | ~ r1_lattice3(X1,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f33957,plain,
    ( ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f33956,f1616])).

fof(f33956,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(subsumption_resolution,[],[f33955,f177])).

fof(f33955,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f33953,f736])).

fof(f33953,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(duplicate_literal_removal,[],[f33952])).

fof(f33952,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f1342,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X0,sK8(X0,X1,X2))
      | ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f1342,plain,
    ( ~ r1_lattice3(sK6,sK7,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f1341,f177])).

fof(f1341,plain,
    ( sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
    | ~ r1_lattice3(sK6,sK7,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)))
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f1337,f736])).

fof(f1337,plain,
    ( sP1(sK7,sK6)
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
    | ~ r1_lattice3(sK6,sK7,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)))
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[],[f1304,f964])).

fof(f964,plain,(
    ! [X0] :
      ( r1_orders_2(sK6,X0,k2_yellow_0(sK5,sK7))
      | ~ r1_lattice3(sK6,sK7,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | v1_xboole_0(u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f963,f140])).

fof(f1304,plain,(
    ! [X6] :
      ( ~ r1_orders_2(sK6,sK8(sK7,sK6,X6),X6)
      | sP1(sK7,sK6)
      | k2_yellow_0(sK5,sK7) = sK10(X6,sK6,sK7)
      | ~ r1_lattice3(sK6,sK7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f1293,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | sP1(X0,X1)
      | ~ r1_orders_2(X1,sK8(X0,X1,X2),X2)
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f34323,plain,
    ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | k2_yellow_0(sK5,sK7) = k2_yellow_0(sK6,sK7) ),
    inference(resolution,[],[f34211,f138])).

fof(f34211,plain,
    ( sP4(sK7,sK6,k2_yellow_0(sK5,sK7))
    | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ),
    inference(resolution,[],[f34104,f177])).

fof(f34104,plain,(
    ! [X49] :
      ( ~ m1_subset_1(X49,u1_struct_0(sK6))
      | sP4(sK7,sK6,X49)
      | k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f34103,f180])).

fof(f34103,plain,(
    ! [X49] :
      ( k2_yellow_0(sK5,sK7) = sK10(k2_yellow_0(sK5,sK7),sK6,sK7)
      | sP4(sK7,sK6,X49)
      | ~ m1_subset_1(X49,u1_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(resolution,[],[f34061,f144])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sK10(X0,X1,X2) != X0
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f34626,plain,
    ( sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(duplicate_literal_removal,[],[f34625])).

fof(f34625,plain,
    ( sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6))
    | ~ sP0(k2_yellow_0(sK5,sK7),sK6,sK7)
    | sP1(sK7,sK6)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f34611,f127])).

fof(f34611,plain,
    ( ~ r1_lattice3(sK6,sK7,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)))
    | sP1(sK7,sK6)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f34608,f34561])).

fof(f34561,plain,
    ( m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f34560,f177])).

fof(f34560,plain,
    ( sP1(sK7,sK6)
    | m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f34555,f736])).

fof(f34555,plain,
    ( sP1(sK7,sK6)
    | m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f34500,f126])).

fof(f34608,plain,
    ( sP1(sK7,sK6)
    | ~ r1_lattice3(sK6,sK7,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)))
    | ~ m1_subset_1(sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[],[f34559,f964])).

fof(f34559,plain,
    ( ~ r1_orders_2(sK6,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),k2_yellow_0(sK5,sK7))
    | sP1(sK7,sK6) ),
    inference(subsumption_resolution,[],[f34558,f177])).

fof(f34558,plain,
    ( sP1(sK7,sK6)
    | ~ r1_orders_2(sK6,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f34554,f736])).

fof(f34554,plain,
    ( sP1(sK7,sK6)
    | ~ r1_orders_2(sK6,sK8(sK7,sK6,k2_yellow_0(sK5,sK7)),k2_yellow_0(sK5,sK7))
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[],[f34500,f128])).

fof(f114,plain,
    ( ~ r2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK5,sK7) != k2_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f78])).

fof(f34949,plain,
    ( ~ sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | k2_yellow_0(sK5,sK7) = k2_yellow_0(sK6,sK7) ),
    inference(resolution,[],[f34859,f138])).

fof(f34859,plain,(
    sP4(sK7,sK6,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f34835,f177])).

fof(f34835,plain,(
    ! [X15] :
      ( ~ m1_subset_1(X15,u1_struct_0(sK6))
      | sP4(sK7,sK6,X15) ) ),
    inference(subsumption_resolution,[],[f34834,f180])).

fof(f34834,plain,(
    ! [X15] :
      ( sP4(sK7,sK6,X15)
      | ~ m1_subset_1(X15,u1_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(resolution,[],[f34770,f144])).

fof(f963,plain,
    ( sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f962,f111])).

fof(f962,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subsumption_resolution,[],[f961,f736])).

fof(f961,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(duplicate_literal_removal,[],[f960])).

fof(f960,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | sP3(k2_yellow_0(sK5,sK7),sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,k2_yellow_0(sK5,sK7)) ),
    inference(resolution,[],[f945,f626])).

fof(f626,plain,(
    ! [X6,X5] :
      ( r1_lattice3(sK5,X6,sK12(X5,sK6,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK6)))
      | sP3(X5,sK6,X6)
      | ~ r1_lattice3(sK6,X6,X5) ) ),
    inference(subsumption_resolution,[],[f622,f141])).

fof(f622,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(sK12(X5,sK6,X6),u1_struct_0(sK6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK6)))
      | r1_lattice3(sK5,X6,sK12(X5,sK6,X6))
      | sP3(X5,sK6,X6)
      | ~ r1_lattice3(sK6,X6,X5) ) ),
    inference(resolution,[],[f618,f142])).

fof(f945,plain,(
    ! [X1] :
      ( ~ r1_lattice3(sK5,sK7,sK12(k2_yellow_0(sK5,sK7),sK6,X1))
      | v1_xboole_0(u1_struct_0(sK6))
      | sP3(k2_yellow_0(sK5,sK7),sK6,X1)
      | ~ r1_lattice3(sK6,X1,k2_yellow_0(sK5,sK7)) ) ),
    inference(subsumption_resolution,[],[f940,f141])).

fof(f940,plain,(
    ! [X1] :
      ( v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(sK12(k2_yellow_0(sK5,sK7),sK6,X1),u1_struct_0(sK6))
      | ~ r1_lattice3(sK5,sK7,sK12(k2_yellow_0(sK5,sK7),sK6,X1))
      | sP3(k2_yellow_0(sK5,sK7),sK6,X1)
      | ~ r1_lattice3(sK6,X1,k2_yellow_0(sK5,sK7)) ) ),
    inference(resolution,[],[f924,f143])).

fof(f924,plain,(
    ! [X0] :
      ( r1_orders_2(sK6,X0,k2_yellow_0(sK5,sK7))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ r1_lattice3(sK5,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f923,f346])).

fof(f923,plain,(
    ! [X0] :
      ( r1_orders_2(sK6,X0,k2_yellow_0(sK5,sK7))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,X0) ) ),
    inference(subsumption_resolution,[],[f913,f177])).

fof(f913,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK5,sK7),u1_struct_0(sK6))
      | r1_orders_2(sK6,X0,k2_yellow_0(sK5,sK7))
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ r1_lattice3(sK5,sK7,X0) ) ),
    inference(resolution,[],[f910,f328])).

fof(f910,plain,(
    ! [X2,X1] :
      ( ~ r1_orders_2(sK5,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | r1_orders_2(sK6,X1,X2)
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f908,f346])).

fof(f908,plain,(
    ! [X2,X1] :
      ( ~ r1_orders_2(sK5,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | r1_orders_2(sK6,X1,X2)
      | v1_xboole_0(u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f906,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t2_subset)).

fof(f906,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f905,f346])).

fof(f905,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1) ) ),
    inference(subsumption_resolution,[],[f904,f107])).

fof(f904,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | r1_orders_2(sK6,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(subsumption_resolution,[],[f903,f110])).

fof(f903,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK6))
      | ~ r1_orders_2(sK5,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_yellow_0(sK6,sK5)
      | r1_orders_2(sK6,X0,X1)
      | ~ l1_orders_2(sK5) ) ),
    inference(resolution,[],[f175,f109])).

fof(f175,plain,(
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
    inference(subsumption_resolution,[],[f167,f156])).

fof(f167,plain,(
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
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
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
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t64_yellow_0.p',t61_yellow_0)).

fof(f113,plain,(
    r2_hidden(k2_yellow_0(sK5,sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f78])).
%------------------------------------------------------------------------------
