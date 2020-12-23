%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t46_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:21 EDT 2019

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 325 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :   24
%              Number of atoms          :  597 (1580 expanded)
%              Number of equality atoms :   42 ( 196 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20682,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f334,f636,f926,f5680,f5692,f14422,f20627,f20653,f20681])).

fof(f20681,plain,
    ( ~ spl8_60
    | ~ spl8_422
    | spl8_867
    | ~ spl8_1546 ),
    inference(avatar_contradiction_clause,[],[f20680])).

fof(f20680,plain,
    ( $false
    | ~ spl8_60
    | ~ spl8_422
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(subsumption_resolution,[],[f20679,f5713])).

fof(f5713,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_60
    | ~ spl8_422 ),
    inference(backward_demodulation,[],[f5679,f619])).

fof(f619,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl8_60
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f5679,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl8_422 ),
    inference(avatar_component_clause,[],[f5678])).

fof(f5678,plain,
    ( spl8_422
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_422])])).

fof(f20679,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_422
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(forward_demodulation,[],[f20678,f5679])).

fof(f20678,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(subsumption_resolution,[],[f20677,f83])).

fof(f83,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) != k1_xboole_0
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( k2_orders_2(X0,k2_struct_0(X0)) != k1_xboole_0
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k2_orders_2(sK0,k2_struct_0(sK0)) != k1_xboole_0
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( k2_orders_2(X0,k2_struct_0(X0)) != k1_xboole_0
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( k2_orders_2(X0,k2_struct_0(X0)) != k1_xboole_0
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k2_orders_2(X0,k2_struct_0(X0)) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k2_orders_2(X0,k2_struct_0(X0)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',t46_orders_2)).

fof(f20677,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(subsumption_resolution,[],[f20676,f84])).

fof(f84,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f20676,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(subsumption_resolution,[],[f20675,f85])).

fof(f85,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f20675,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(subsumption_resolution,[],[f20674,f86])).

fof(f86,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f20674,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(subsumption_resolution,[],[f20673,f87])).

fof(f87,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f20673,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_867
    | ~ spl8_1546 ),
    inference(subsumption_resolution,[],[f20671,f12212])).

fof(f12212,plain,
    ( ~ v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl8_867 ),
    inference(avatar_component_clause,[],[f12211])).

fof(f12211,plain,
    ( spl8_867
  <=> ~ v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_867])])).

fof(f20671,plain,
    ( v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1546 ),
    inference(superposition,[],[f20626,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',d13_orders_2)).

fof(f20626,plain,
    ( v1_xboole_0(a_2_1_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl8_1546 ),
    inference(avatar_component_clause,[],[f20625])).

fof(f20625,plain,
    ( spl8_1546
  <=> v1_xboole_0(a_2_1_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1546])])).

fof(f20653,plain,(
    ~ spl8_1544 ),
    inference(avatar_contradiction_clause,[],[f20651])).

fof(f20651,plain,
    ( $false
    | ~ spl8_1544 ),
    inference(resolution,[],[f20620,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',existence_m1_subset_1)).

fof(f20620,plain,
    ( ! [X0] : ~ m1_subset_1(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl8_1544 ),
    inference(avatar_component_clause,[],[f20619])).

fof(f20619,plain,
    ( spl8_1544
  <=> ! [X0] : ~ m1_subset_1(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1544])])).

fof(f20627,plain,
    ( spl8_1544
    | spl8_1546
    | spl8_59
    | ~ spl8_60
    | ~ spl8_422 ),
    inference(avatar_split_clause,[],[f20602,f5678,f618,f596,f20625,f20619])).

fof(f596,plain,
    ( spl8_59
  <=> ~ v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f20602,plain,
    ( ! [X0] :
        ( v1_xboole_0(a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) )
    | ~ spl8_59
    | ~ spl8_60
    | ~ spl8_422 ),
    inference(resolution,[],[f20593,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',t2_subset)).

fof(f20593,plain,
    ( ! [X0] : ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl8_59
    | ~ spl8_60
    | ~ spl8_422 ),
    inference(subsumption_resolution,[],[f20592,f5713])).

fof(f20592,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl8_59
    | ~ spl8_422 ),
    inference(subsumption_resolution,[],[f20591,f597])).

fof(f597,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f596])).

fof(f20591,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl8_422 ),
    inference(duplicate_literal_removal,[],[f20584])).

fof(f20584,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) )
    | ~ spl8_422 ),
    inference(resolution,[],[f6421,f5876])).

fof(f5876,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(X0,sK0,X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) )
    | ~ spl8_422 ),
    inference(forward_demodulation,[],[f5731,f5679])).

fof(f5731,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(X0,sK0,X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) )
    | ~ spl8_422 ),
    inference(backward_demodulation,[],[f5679,f843])).

fof(f843,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f842,f83])).

fof(f842,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(X0,sK0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f841,f84])).

fof(f841,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f840,f85])).

fof(f840,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f839,f87])).

fof(f839,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | m1_subset_1(sK5(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f114,f86])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK4(X1,X2,X3))
                & r2_hidden(sK4(X1,X2,X3),X2)
                & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK5(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f75,f77,f76])).

fof(f76,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK4(X1,X2,X3))
        & r2_hidden(sK4(X1,X2,X3),X2)
        & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK5(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',fraenkel_a_2_1_orders_2)).

fof(f6421,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(X1,sK0,X0),X0)
        | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl8_422 ),
    inference(resolution,[],[f5781,f100])).

fof(f5781,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(X0,sK0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) )
    | ~ spl8_422 ),
    inference(backward_demodulation,[],[f5679,f1861])).

fof(f1861,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f1860,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',t4_subset)).

fof(f1860,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X0,sK0,X1),X1)
      | ~ m1_subset_1(sK5(X0,sK0,X1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1856,f87])).

fof(f1856,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X0,sK0,X1),X1)
      | ~ m1_subset_1(sK5(X0,sK0,X1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f1433,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(condensation,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',irreflexivity_r2_orders_2)).

fof(f1433,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,sK5(X2,sK0,X1),X0)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1432,f83])).

fof(f1432,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK5(X2,sK0,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1431,f84])).

fof(f1431,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK5(X2,sK0,X1),X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1430,f85])).

fof(f1430,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK5(X2,sK0,X1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1429,f87])).

fof(f1429,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | r2_orders_2(sK0,sK5(X2,sK0,X1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1307,f86])).

fof(f1307,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_orders_2(X1,sK5(X0,X1,X2),X6)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f116,f121])).

fof(f116,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK5(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f14422,plain,(
    ~ spl8_866 ),
    inference(avatar_contradiction_clause,[],[f14421])).

fof(f14421,plain,
    ( $false
    | ~ spl8_866 ),
    inference(subsumption_resolution,[],[f14412,f88])).

fof(f88,plain,(
    k2_orders_2(sK0,k2_struct_0(sK0)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

fof(f14412,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = k1_xboole_0
    | ~ spl8_866 ),
    inference(resolution,[],[f12215,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',t6_boole)).

fof(f12215,plain,
    ( v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl8_866 ),
    inference(avatar_component_clause,[],[f12214])).

fof(f12214,plain,
    ( spl8_866
  <=> v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_866])])).

fof(f5692,plain,
    ( ~ spl8_6
    | spl8_113 ),
    inference(avatar_contradiction_clause,[],[f5691])).

fof(f5691,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_113 ),
    inference(subsumption_resolution,[],[f5690,f240])).

fof(f240,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl8_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f5690,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl8_113 ),
    inference(subsumption_resolution,[],[f5689,f125])).

fof(f125,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',d10_xboole_0)).

fof(f5689,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl8_113 ),
    inference(superposition,[],[f5681,f91])).

fof(f91,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',d3_struct_0)).

fof(f5681,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl8_113 ),
    inference(resolution,[],[f1064,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',t3_subset)).

fof(f1064,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1063,plain,
    ( spl8_113
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f5680,plain,
    ( ~ spl8_113
    | spl8_422
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f5669,f618,f5678,f1063])).

fof(f5669,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl8_60 ),
    inference(resolution,[],[f205,f619])).

fof(f205,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | X6 = X7
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7)) ) ),
    inference(resolution,[],[f144,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f144,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | X6 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) ) ),
    inference(resolution,[],[f106,f110])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f926,plain,
    ( ~ spl8_6
    | ~ spl8_58 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f924,f83])).

fof(f924,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f918,f240])).

fof(f918,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_58 ),
    inference(resolution,[],[f600,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',fc5_struct_0)).

fof(f600,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl8_58
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f636,plain,
    ( ~ spl8_6
    | spl8_61 ),
    inference(avatar_contradiction_clause,[],[f635])).

fof(f635,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f630,f240])).

fof(f630,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl8_61 ),
    inference(resolution,[],[f622,f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',dt_k2_struct_0)).

fof(f622,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl8_61
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f334,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f332,f87])).

fof(f332,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f243,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t46_orders_2.p',dt_l1_orders_2)).

fof(f243,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl8_7
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
%------------------------------------------------------------------------------
