%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1647+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:15 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 781 expanded)
%              Number of leaves         :   39 ( 298 expanded)
%              Depth                    :   13
%              Number of atoms          :  799 (4925 expanded)
%              Number of equality atoms :   37 ( 121 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1834,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f108,f119,f185,f194,f196,f220,f226,f238,f307,f392,f434,f466,f472,f484,f490,f525,f651,f730,f1735,f1737,f1810,f1833])).

fof(f1833,plain,
    ( ~ spl7_6
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_16
    | spl7_32 ),
    inference(avatar_contradiction_clause,[],[f1832])).

fof(f1832,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_16
    | spl7_32 ),
    inference(subsumption_resolution,[],[f650,f1806])).

fof(f1806,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1805,f596])).

fof(f596,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl7_16 ),
    inference(resolution,[],[f225,f77])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f225,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl7_16
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f1805,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1799,f219])).

fof(f219,plain,
    ( m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_15
  <=> m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1799,plain,
    ( ~ m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(resolution,[],[f1741,f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_6
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK2)
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1741,plain,
    ( r1_orders_2(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK3(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f184,f147])).

fof(f147,plain,(
    ! [X7] : k9_subset_1(u1_struct_0(sK0),X7,sK2) = k3_xboole_0(X7,sK2) ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      | ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) )
    & v12_waybel_0(sK2,sK0)
    & v12_waybel_0(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                  | ~ v12_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
                & v12_waybel_0(X2,X0)
                & v12_waybel_0(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
                | ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) )
              & v12_waybel_0(X2,sK0)
              & v12_waybel_0(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              | ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) )
            & v12_waybel_0(X2,sK0)
            & v12_waybel_0(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
            | ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) )
          & v12_waybel_0(X2,sK0)
          & v12_waybel_0(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          | ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) )
        & v12_waybel_0(X2,sK0)
        & v12_waybel_0(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
        | ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) )
      & v12_waybel_0(sK2,sK0)
      & v12_waybel_0(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v12_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v12_waybel_0(X2,X0)
              & v12_waybel_0(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v12_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v12_waybel_0(X2,X0)
              & v12_waybel_0(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v12_waybel_0(X2,X0)
                    & v12_waybel_0(X1,X0) )
                 => ( v12_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v12_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v12_waybel_0(X2,X0)
                  & v12_waybel_0(X1,X0) )
               => ( v12_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                  & v12_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_0)).

fof(f184,plain,
    ( r1_orders_2(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_11
  <=> r1_orders_2(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f650,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | spl7_32 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl7_32
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f1810,plain,
    ( ~ spl7_4
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_16
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f1809])).

fof(f1809,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_16
    | spl7_31 ),
    inference(subsumption_resolution,[],[f1808,f646])).

fof(f646,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | spl7_31 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl7_31
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f1808,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f1807,f595])).

fof(f595,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f225,f78])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1807,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1800,f219])).

fof(f1800,plain,
    ( ~ m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(resolution,[],[f1741,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_4
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1737,plain,
    ( ~ spl7_34
    | ~ spl7_27
    | ~ spl7_6
    | ~ spl7_23
    | spl7_30 ),
    inference(avatar_split_clause,[],[f1736,f481,f431,f117,f463,f727])).

fof(f727,plain,
    ( spl7_34
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f463,plain,
    ( spl7_27
  <=> m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f431,plain,
    ( spl7_23
  <=> r1_orders_2(sK0,sK4(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f481,plain,
    ( spl7_30
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1736,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl7_6
    | ~ spl7_23
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1658,f741])).

fof(f741,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | spl7_30 ),
    inference(resolution,[],[f483,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f483,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f481])).

fof(f1658,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl7_6
    | ~ spl7_23 ),
    inference(resolution,[],[f1581,f118])).

fof(f1581,plain,
    ( r1_orders_2(sK0,sK4(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f433,f946])).

fof(f946,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f126,f47])).

fof(f126,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_xboole_0(sK1,X2) ) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f433,plain,
    ( r1_orders_2(sK0,sK4(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f431])).

fof(f1735,plain,
    ( ~ spl7_33
    | ~ spl7_27
    | ~ spl7_4
    | ~ spl7_23
    | spl7_30 ),
    inference(avatar_split_clause,[],[f1734,f481,f431,f106,f463,f723])).

fof(f723,plain,
    ( spl7_33
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f1734,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl7_4
    | ~ spl7_23
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1659,f740])).

fof(f740,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | spl7_30 ),
    inference(resolution,[],[f483,f80])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1659,plain,
    ( ~ m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl7_4
    | ~ spl7_23 ),
    inference(resolution,[],[f1581,f107])).

fof(f730,plain,
    ( spl7_33
    | spl7_34
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f712,f469,f727,f723])).

fof(f469,plain,
    ( spl7_28
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f712,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f471,f81])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f471,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f469])).

fof(f651,plain,
    ( ~ spl7_31
    | ~ spl7_32
    | spl7_18 ),
    inference(avatar_split_clause,[],[f634,f235,f648,f644])).

fof(f235,plain,
    ( spl7_18
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f634,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | spl7_18 ),
    inference(resolution,[],[f237,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f237,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f525,plain,
    ( ~ spl7_19
    | spl7_25 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl7_19
    | spl7_25 ),
    inference(subsumption_resolution,[],[f523,f46])).

fof(f523,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_19
    | spl7_25 ),
    inference(subsumption_resolution,[],[f522,f47])).

fof(f522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_19
    | spl7_25 ),
    inference(subsumption_resolution,[],[f511,f455])).

fof(f455,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl7_25
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f511,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_19 ),
    inference(superposition,[],[f410,f51])).

fof(f410,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl7_19
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f490,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | spl7_19 ),
    inference(subsumption_resolution,[],[f488,f46])).

fof(f488,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_19 ),
    inference(subsumption_resolution,[],[f485,f47])).

fof(f485,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_19 ),
    inference(resolution,[],[f411,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f411,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f409])).

fof(f484,plain,
    ( ~ spl7_25
    | ~ spl7_30
    | spl7_2 ),
    inference(avatar_split_clause,[],[f479,f87,f481,f453])).

fof(f87,plain,
    ( spl7_2
  <=> v12_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f479,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f447,f45])).

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f447,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_2 ),
    inference(resolution,[],[f442,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).

fof(f32,plain,(
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
            & r1_orders_2(X0,X3,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f442,plain,
    ( ~ v12_waybel_0(k2_xboole_0(sK1,sK2),sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f441,f46])).

fof(f441,plain,
    ( ~ v12_waybel_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f406,f47])).

fof(f406,plain,
    ( ~ v12_waybel_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(superposition,[],[f89,f51])).

fof(f89,plain,
    ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f472,plain,
    ( ~ spl7_25
    | spl7_28
    | spl7_2 ),
    inference(avatar_split_clause,[],[f467,f87,f469,f453])).

fof(f467,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f445,f45])).

fof(f445,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_2 ),
    inference(resolution,[],[f442,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f466,plain,
    ( ~ spl7_25
    | spl7_27
    | spl7_2 ),
    inference(avatar_split_clause,[],[f461,f87,f463,f453])).

fof(f461,plain,
    ( m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f444,f45])).

fof(f444,plain,
    ( m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_2 ),
    inference(resolution,[],[f442,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f434,plain,
    ( ~ spl7_19
    | spl7_23
    | spl7_2 ),
    inference(avatar_split_clause,[],[f429,f87,f431,f409])).

fof(f429,plain,
    ( r1_orders_2(sK0,sK4(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f404,f45])).

fof(f404,plain,
    ( r1_orders_2(sK0,sK4(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_2 ),
    inference(resolution,[],[f89,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f392,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f390,f276])).

fof(f276,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f261,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f261,plain,(
    ! [X8] : m1_subset_1(k3_xboole_0(X8,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f132,f131])).

fof(f131,plain,(
    ! [X7] : k9_subset_1(u1_struct_0(sK0),X7,sK1) = k3_xboole_0(X7,sK1) ),
    inference(resolution,[],[f46,f54])).

fof(f132,plain,(
    ! [X8] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X8,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f46,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f390,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_7 ),
    inference(forward_demodulation,[],[f162,f147])).

fof(f162,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl7_7
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f307,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl7_13 ),
    inference(resolution,[],[f276,f209])).

fof(f209,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl7_13
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f238,plain,
    ( ~ spl7_13
    | ~ spl7_18
    | spl7_1 ),
    inference(avatar_split_clause,[],[f233,f83,f235,f207])).

fof(f83,plain,
    ( spl7_1
  <=> v12_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f233,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f201,f45])).

fof(f201,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_1 ),
    inference(resolution,[],[f192,f61])).

fof(f192,plain,
    ( ~ v12_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f157,f47])).

fof(f157,plain,
    ( ~ v12_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f85,f54])).

fof(f85,plain,
    ( ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f226,plain,
    ( ~ spl7_13
    | spl7_16
    | spl7_1 ),
    inference(avatar_split_clause,[],[f221,f83,f223,f207])).

fof(f221,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f199,f45])).

fof(f199,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_1 ),
    inference(resolution,[],[f192,f59])).

fof(f220,plain,
    ( ~ spl7_13
    | spl7_15
    | spl7_1 ),
    inference(avatar_split_clause,[],[f215,f83,f217,f207])).

fof(f215,plain,
    ( m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f198,f45])).

fof(f198,plain,
    ( m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_1 ),
    inference(resolution,[],[f192,f58])).

fof(f196,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f115,f47])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f194,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f104,f46])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f185,plain,
    ( ~ spl7_7
    | spl7_11
    | spl7_1 ),
    inference(avatar_split_clause,[],[f180,f83,f182,f160])).

fof(f180,plain,
    ( r1_orders_2(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f155,f45])).

fof(f155,plain,
    ( r1_orders_2(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK3(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl7_1 ),
    inference(resolution,[],[f85,f60])).

fof(f119,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f111,f117,f113])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f110,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f109,f45])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f49,f56])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f100,f106,f102])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f99,f62])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f98,f45])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f48,f56])).

fof(f48,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f50,f87,f83])).

fof(f50,plain,
    ( ~ v12_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v12_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
