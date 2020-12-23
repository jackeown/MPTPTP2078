%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:04 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  147 (1817 expanded)
%              Number of leaves         :   25 ( 399 expanded)
%              Depth                    :   18
%              Number of atoms          :  592 (11960 expanded)
%              Number of equality atoms :   39 ( 143 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f170,f220,f243,f247,f251,f444,f470,f509,f539,f592,f608,f723,f781,f798])).

fof(f798,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | spl7_26 ),
    inference(unit_resulting_resolution,[],[f134,f722,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f722,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f720])).

fof(f720,plain,
    ( spl7_26
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f134,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f130,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f130,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f114,f112,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f112,plain,(
    m1_subset_1(sK5(sK0,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f41,f35,f35,f96,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(f96,plain,(
    r1_orders_2(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f41,f37,f35,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f114,plain,(
    r2_hidden(sK2,sK5(sK0,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f41,f35,f35,f96,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(X2,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f781,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | spl7_25 ),
    inference(unit_resulting_resolution,[],[f77,f145,f718,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f718,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f716])).

fof(f716,plain,
    ( spl7_25
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f145,plain,(
    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f135,f72])).

fof(f135,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f130,f55])).

fof(f36,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f723,plain,
    ( ~ spl7_25
    | ~ spl7_26
    | ~ spl7_1
    | spl7_3
    | spl7_3
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f661,f507,f468,f167,f167,f99,f720,f716])).

fof(f99,plain,
    ( spl7_1
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f167,plain,
    ( spl7_3
  <=> r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f468,plain,
    ( spl7_19
  <=> ! [X29,X28] :
        ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X29,a_2_1_orders_2(sK0,X28))
        | r2_hidden(sK4(sK0,X28,X29),X28)
        | ~ m1_subset_1(X29,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f507,plain,
    ( spl7_20
  <=> ! [X27,X26] :
        ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X27,a_2_1_orders_2(sK0,X26))
        | ~ r2_orders_2(sK0,X27,sK4(sK0,X26,X27))
        | ~ m1_subset_1(X27,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f661,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_3
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f659,f149])).

fof(f149,plain,(
    k2_orders_2(sK0,k2_tarski(sK2,sK2)) = a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f41,f37,f40,f39,f143,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f143,plain,(
    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f134,f72])).

fof(f39,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f659,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_3
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(superposition,[],[f508,f640])).

fof(f640,plain,
    ( sK2 = sK4(sK0,k2_tarski(sK2,sK2),sK1)
    | spl7_3
    | ~ spl7_19 ),
    inference(duplicate_literal_removal,[],[f633])).

fof(f633,plain,
    ( sK2 = sK4(sK0,k2_tarski(sK2,sK2),sK1)
    | sK2 = sK4(sK0,k2_tarski(sK2,sK2),sK1)
    | spl7_3
    | ~ spl7_19 ),
    inference(resolution,[],[f594,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f594,plain,
    ( r2_hidden(sK4(sK0,k2_tarski(sK2,sK2),sK1),k2_tarski(sK2,sK2))
    | spl7_3
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f36,f169,f480])).

fof(f480,plain,
    ( ! [X8] :
        ( r2_hidden(X8,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
        | r2_hidden(sK4(sK0,k2_tarski(sK2,sK2),X8),k2_tarski(sK2,sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f475,f149])).

fof(f475,plain,
    ( ! [X8] :
        ( r2_hidden(X8,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))
        | r2_hidden(sK4(sK0,k2_tarski(sK2,sK2),X8),k2_tarski(sK2,sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl7_19 ),
    inference(resolution,[],[f469,f143])).

fof(f469,plain,
    ( ! [X28,X29] :
        ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X29,a_2_1_orders_2(sK0,X28))
        | r2_hidden(sK4(sK0,X28,X29),X28)
        | ~ m1_subset_1(X29,u1_struct_0(sK0)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f468])).

fof(f169,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f167])).

fof(f508,plain,
    ( ! [X26,X27] :
        ( ~ r2_orders_2(sK0,X27,sK4(sK0,X26,X27))
        | r2_hidden(X27,a_2_1_orders_2(sK0,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X27,u1_struct_0(sK0)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f507])).

fof(f608,plain,
    ( ~ spl7_2
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f187,f189,f169,f55])).

fof(f189,plain,
    ( m1_subset_1(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f79,f140,f42])).

fof(f140,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_orders_2(sK0,k2_tarski(sK2,sK2))))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f125,f136])).

fof(f136,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f35,f130,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f125,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f105,f72])).

fof(f105,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_2
  <=> r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f79,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f187,plain,
    ( ~ v1_xboole_0(k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f77,f140,f52])).

fof(f592,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_18
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_18
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f187,f189,f570,f55])).

fof(f570,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | spl7_1
    | ~ spl7_18
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f567,f149])).

fof(f567,plain,
    ( ~ r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))
    | spl7_1
    | ~ spl7_18
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f100,f35,f79,f143,f564])).

fof(f564,plain,
    ( ! [X2,X0,X1] :
        ( r2_orders_2(sK0,X0,X2)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X1) )
    | ~ spl7_18
    | ~ spl7_21 ),
    inference(duplicate_literal_removal,[],[f563])).

fof(f563,plain,
    ( ! [X2,X0,X1] :
        ( r2_orders_2(sK0,X0,X2)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_18
    | ~ spl7_21 ),
    inference(superposition,[],[f538,f443])).

fof(f443,plain,
    ( ! [X4,X5] :
        ( sK3(X5,sK0,X4) = X5
        | ~ r2_hidden(X5,a_2_1_orders_2(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl7_18
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,a_2_1_orders_2(sK0,X4))
        | sK3(X5,sK0,X4) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f538,plain,
    ( ! [X2,X3,X1] :
        ( r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
        | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X1) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl7_21
  <=> ! [X1,X3,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f100,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f539,plain,
    ( spl7_21
    | spl7_5
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f82,f213,f236,f232,f209,f537])).

fof(f209,plain,
    ( spl7_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f232,plain,
    ( spl7_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f236,plain,
    ( spl7_9
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f213,plain,
    ( spl7_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f82,plain,(
    ! [X2,X3,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | r2_orders_2(sK0,sK3(X3,sK0,X1),X2)
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,sK3(X0,X1,X2),X4)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f509,plain,
    ( spl7_20
    | spl7_5
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f94,f213,f236,f232,f209,f507])).

fof(f94,plain,(
    ! [X26,X27] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X27,sK4(sK0,X26,X27))
      | r2_hidden(X27,a_2_1_orders_2(sK0,X26)) ) ),
    inference(resolution,[],[f41,f73])).

fof(f73,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_orders_2(X1,X3,sK4(X1,X2,X3))
      | r2_hidden(X3,a_2_1_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r2_orders_2(X1,X3,sK4(X1,X2,X3))
      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f470,plain,
    ( spl7_19
    | spl7_5
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f95,f213,f236,f232,f209,f468])).

fof(f95,plain,(
    ! [X28,X29] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X29,u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X28,X29),X28)
      | r2_hidden(X29,a_2_1_orders_2(sK0,X28)) ) ),
    inference(resolution,[],[f41,f74])).

fof(f74,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(sK4(X1,X2,X3),X2)
      | r2_hidden(X3,a_2_1_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | r2_hidden(sK4(X1,X2,X3),X2)
      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f444,plain,
    ( spl7_18
    | spl7_5
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f83,f213,f236,f232,f209,f442])).

fof(f83,plain,(
    ! [X4,X5] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X5,sK0,X4) = X5
      | ~ r2_hidden(X5,a_2_1_orders_2(sK0,X4)) ) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f251,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f37,f211])).

fof(f211,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f209])).

fof(f247,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl7_9 ),
    inference(unit_resulting_resolution,[],[f39,f238])).

fof(f238,plain,
    ( ~ v4_orders_2(sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f236])).

fof(f243,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f40,f234])).

fof(f234,plain,
    ( ~ v5_orders_2(sK0)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f232])).

fof(f220,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f38,f215])).

fof(f215,plain,
    ( ~ v3_orders_2(sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f170,plain,
    ( ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f142,f167,f99])).

fof(f142,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f34,f136])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f33,f103,f99])).

fof(f33,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (18683)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.45  % (18689)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (18699)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (18693)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (18706)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (18685)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (18690)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (18710)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (18688)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (18702)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (18694)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (18701)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (18710)Refutation not found, incomplete strategy% (18710)------------------------------
% 0.20/0.54  % (18710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18710)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18710)Memory used [KB]: 1791
% 0.20/0.54  % (18710)Time elapsed: 0.097 s
% 0.20/0.54  % (18710)------------------------------
% 0.20/0.54  % (18710)------------------------------
% 0.20/0.55  % (18681)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.55  % (18704)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (18709)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (18708)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (18698)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (18686)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.55  % (18684)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (18709)Refutation not found, incomplete strategy% (18709)------------------------------
% 0.20/0.55  % (18709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18692)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (18703)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.54/0.56  % (18695)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.54/0.56  % (18697)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.54/0.56  % (18695)Refutation not found, incomplete strategy% (18695)------------------------------
% 1.54/0.56  % (18695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (18695)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (18695)Memory used [KB]: 1791
% 1.54/0.56  % (18695)Time elapsed: 0.156 s
% 1.54/0.56  % (18695)------------------------------
% 1.54/0.56  % (18695)------------------------------
% 1.54/0.56  % (18696)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.54/0.56  % (18700)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.56  % (18687)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.56  % (18682)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.54/0.57  % (18697)Refutation not found, incomplete strategy% (18697)------------------------------
% 1.54/0.57  % (18697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (18691)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.54/0.57  % (18709)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (18709)Memory used [KB]: 10746
% 1.54/0.57  % (18709)Time elapsed: 0.142 s
% 1.54/0.57  % (18709)------------------------------
% 1.54/0.57  % (18709)------------------------------
% 1.54/0.57  % (18691)Refutation not found, incomplete strategy% (18691)------------------------------
% 1.54/0.57  % (18691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (18697)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (18697)Memory used [KB]: 10746
% 1.54/0.57  % (18697)Time elapsed: 0.144 s
% 1.54/0.57  % (18697)------------------------------
% 1.54/0.57  % (18697)------------------------------
% 1.54/0.57  % (18705)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.67/0.58  % (18707)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.67/0.58  % (18691)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (18691)Memory used [KB]: 10746
% 1.67/0.58  % (18691)Time elapsed: 0.144 s
% 1.67/0.58  % (18691)------------------------------
% 1.67/0.58  % (18691)------------------------------
% 1.67/0.59  % (18706)Refutation found. Thanks to Tanya!
% 1.67/0.59  % SZS status Theorem for theBenchmark
% 1.67/0.59  % SZS output start Proof for theBenchmark
% 1.67/0.59  fof(f799,plain,(
% 1.67/0.59    $false),
% 1.67/0.59    inference(avatar_sat_refutation,[],[f106,f170,f220,f243,f247,f251,f444,f470,f509,f539,f592,f608,f723,f781,f798])).
% 1.67/0.59  fof(f798,plain,(
% 1.67/0.59    spl7_26),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f790])).
% 1.67/0.59  fof(f790,plain,(
% 1.67/0.59    $false | spl7_26),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f134,f722,f72])).
% 1.67/0.59  fof(f72,plain,(
% 1.67/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))) )),
% 1.67/0.59    inference(definition_unfolding,[],[f53,f54])).
% 1.67/0.59  fof(f54,plain,(
% 1.67/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f2])).
% 1.67/0.59  fof(f2,axiom,(
% 1.67/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.67/0.59  fof(f53,plain,(
% 1.67/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f28])).
% 1.67/0.59  fof(f28,plain,(
% 1.67/0.59    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f3])).
% 1.67/0.59  fof(f3,axiom,(
% 1.67/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.67/0.59  fof(f722,plain,(
% 1.67/0.59    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_26),
% 1.67/0.59    inference(avatar_component_clause,[],[f720])).
% 1.67/0.59  fof(f720,plain,(
% 1.67/0.59    spl7_26 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.67/0.59  fof(f134,plain,(
% 1.67/0.59    r2_hidden(sK2,u1_struct_0(sK0))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f35,f130,f55])).
% 1.67/0.59  fof(f55,plain,(
% 1.67/0.59    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f30])).
% 1.67/0.59  fof(f30,plain,(
% 1.67/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.67/0.59    inference(flattening,[],[f29])).
% 1.67/0.59  fof(f29,plain,(
% 1.67/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f4])).
% 1.67/0.59  fof(f4,axiom,(
% 1.67/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.67/0.59  fof(f130,plain,(
% 1.67/0.59    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f114,f112,f52])).
% 1.67/0.59  fof(f52,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f27,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f6])).
% 1.67/0.59  fof(f6,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.67/0.59  fof(f112,plain,(
% 1.67/0.59    m1_subset_1(sK5(sK0,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f38,f41,f35,f35,f96,f61])).
% 1.67/0.59  fof(f61,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f32])).
% 1.67/0.59  fof(f32,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.67/0.59    inference(flattening,[],[f31])).
% 1.67/0.59  fof(f31,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f14])).
% 1.67/0.59  fof(f14,plain,(
% 1.67/0.59    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 1.67/0.59    inference(rectify,[],[f11])).
% 1.67/0.59  fof(f11,axiom,(
% 1.67/0.59    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).
% 1.67/0.59  fof(f96,plain,(
% 1.67/0.59    r1_orders_2(sK0,sK2,sK2)),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f38,f41,f37,f35,f51])).
% 1.67/0.59  fof(f51,plain,(
% 1.67/0.59    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f26])).
% 1.67/0.59  fof(f26,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(flattening,[],[f25])).
% 1.67/0.59  fof(f25,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f10])).
% 1.67/0.59  fof(f10,axiom,(
% 1.67/0.59    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 1.67/0.59  fof(f37,plain,(
% 1.67/0.59    ~v2_struct_0(sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f16,plain,(
% 1.67/0.59    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.67/0.59    inference(flattening,[],[f15])).
% 1.67/0.59  fof(f15,plain,(
% 1.67/0.59    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f13])).
% 1.67/0.59  fof(f13,negated_conjecture,(
% 1.67/0.59    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.67/0.59    inference(negated_conjecture,[],[f12])).
% 1.67/0.59  fof(f12,conjecture,(
% 1.67/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).
% 1.67/0.59  fof(f41,plain,(
% 1.67/0.59    l1_orders_2(sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f38,plain,(
% 1.67/0.59    v3_orders_2(sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f114,plain,(
% 1.67/0.59    r2_hidden(sK2,sK5(sK0,sK2,sK2))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f38,f41,f35,f35,f96,f63])).
% 1.67/0.59  fof(f63,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | r2_hidden(X2,sK5(X0,X1,X2))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f32])).
% 1.67/0.59  fof(f35,plain,(
% 1.67/0.59    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f781,plain,(
% 1.67/0.59    spl7_25),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f762])).
% 1.67/0.59  fof(f762,plain,(
% 1.67/0.59    $false | spl7_25),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f77,f145,f718,f42])).
% 1.67/0.59  fof(f42,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f18])).
% 1.67/0.59  fof(f18,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.67/0.59    inference(flattening,[],[f17])).
% 1.67/0.59  fof(f17,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.67/0.59    inference(ennf_transformation,[],[f5])).
% 1.67/0.59  fof(f5,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.67/0.59  fof(f718,plain,(
% 1.67/0.59    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl7_25),
% 1.67/0.59    inference(avatar_component_clause,[],[f716])).
% 1.67/0.59  fof(f716,plain,(
% 1.67/0.59    spl7_25 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.67/0.59  fof(f145,plain,(
% 1.67/0.59    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f135,f72])).
% 1.67/0.59  fof(f135,plain,(
% 1.67/0.59    r2_hidden(sK1,u1_struct_0(sK0))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f36,f130,f55])).
% 1.67/0.59  fof(f36,plain,(
% 1.67/0.59    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f77,plain,(
% 1.67/0.59    ( ! [X0,X3] : (r2_hidden(X3,k2_tarski(X0,X3))) )),
% 1.67/0.59    inference(equality_resolution,[],[f76])).
% 1.67/0.59  fof(f76,plain,(
% 1.67/0.59    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_tarski(X0,X3) != X2) )),
% 1.67/0.59    inference(equality_resolution,[],[f70])).
% 1.67/0.59  fof(f70,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.67/0.59    inference(cnf_transformation,[],[f1])).
% 1.67/0.59  fof(f1,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.67/0.59  fof(f723,plain,(
% 1.67/0.59    ~spl7_25 | ~spl7_26 | ~spl7_1 | spl7_3 | spl7_3 | ~spl7_19 | ~spl7_20),
% 1.67/0.59    inference(avatar_split_clause,[],[f661,f507,f468,f167,f167,f99,f720,f716])).
% 1.67/0.59  fof(f99,plain,(
% 1.67/0.59    spl7_1 <=> r2_orders_2(sK0,sK1,sK2)),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.67/0.59  fof(f167,plain,(
% 1.67/0.59    spl7_3 <=> r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.67/0.59  fof(f468,plain,(
% 1.67/0.59    spl7_19 <=> ! [X29,X28] : (~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X29,a_2_1_orders_2(sK0,X28)) | r2_hidden(sK4(sK0,X28,X29),X28) | ~m1_subset_1(X29,u1_struct_0(sK0)))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.67/0.59  fof(f507,plain,(
% 1.67/0.59    spl7_20 <=> ! [X27,X26] : (~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X27,a_2_1_orders_2(sK0,X26)) | ~r2_orders_2(sK0,X27,sK4(sK0,X26,X27)) | ~m1_subset_1(X27,u1_struct_0(sK0)))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.67/0.59  fof(f661,plain,(
% 1.67/0.59    r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | ~r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl7_3 | ~spl7_19 | ~spl7_20)),
% 1.67/0.59    inference(forward_demodulation,[],[f659,f149])).
% 1.67/0.59  fof(f149,plain,(
% 1.67/0.59    k2_orders_2(sK0,k2_tarski(sK2,sK2)) = a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f38,f41,f37,f40,f39,f143,f43])).
% 1.67/0.59  fof(f43,plain,(
% 1.67/0.59    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f20])).
% 1.67/0.59  fof(f20,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(flattening,[],[f19])).
% 1.67/0.59  fof(f19,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f7])).
% 1.67/0.59  fof(f7,axiom,(
% 1.67/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 1.67/0.59  fof(f143,plain,(
% 1.67/0.59    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f134,f72])).
% 1.67/0.59  fof(f39,plain,(
% 1.67/0.59    v4_orders_2(sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f40,plain,(
% 1.67/0.59    v5_orders_2(sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f659,plain,(
% 1.67/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl7_3 | ~spl7_19 | ~spl7_20)),
% 1.67/0.59    inference(superposition,[],[f508,f640])).
% 1.67/0.59  fof(f640,plain,(
% 1.67/0.59    sK2 = sK4(sK0,k2_tarski(sK2,sK2),sK1) | (spl7_3 | ~spl7_19)),
% 1.67/0.59    inference(duplicate_literal_removal,[],[f633])).
% 1.67/0.59  fof(f633,plain,(
% 1.67/0.59    sK2 = sK4(sK0,k2_tarski(sK2,sK2),sK1) | sK2 = sK4(sK0,k2_tarski(sK2,sK2),sK1) | (spl7_3 | ~spl7_19)),
% 1.67/0.59    inference(resolution,[],[f594,f80])).
% 1.67/0.59  fof(f80,plain,(
% 1.67/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.67/0.59    inference(equality_resolution,[],[f68])).
% 1.67/0.59  fof(f68,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.67/0.59    inference(cnf_transformation,[],[f1])).
% 1.67/0.59  fof(f594,plain,(
% 1.67/0.59    r2_hidden(sK4(sK0,k2_tarski(sK2,sK2),sK1),k2_tarski(sK2,sK2)) | (spl7_3 | ~spl7_19)),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f36,f169,f480])).
% 1.67/0.59  fof(f480,plain,(
% 1.67/0.59    ( ! [X8] : (r2_hidden(X8,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | r2_hidden(sK4(sK0,k2_tarski(sK2,sK2),X8),k2_tarski(sK2,sK2)) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | ~spl7_19),
% 1.67/0.59    inference(forward_demodulation,[],[f475,f149])).
% 1.67/0.59  fof(f475,plain,(
% 1.67/0.59    ( ! [X8] : (r2_hidden(X8,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) | r2_hidden(sK4(sK0,k2_tarski(sK2,sK2),X8),k2_tarski(sK2,sK2)) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | ~spl7_19),
% 1.67/0.59    inference(resolution,[],[f469,f143])).
% 1.67/0.59  fof(f469,plain,(
% 1.67/0.59    ( ! [X28,X29] : (~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X29,a_2_1_orders_2(sK0,X28)) | r2_hidden(sK4(sK0,X28,X29),X28) | ~m1_subset_1(X29,u1_struct_0(sK0))) ) | ~spl7_19),
% 1.67/0.59    inference(avatar_component_clause,[],[f468])).
% 1.67/0.59  fof(f169,plain,(
% 1.67/0.59    ~r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | spl7_3),
% 1.67/0.59    inference(avatar_component_clause,[],[f167])).
% 1.67/0.59  fof(f508,plain,(
% 1.67/0.59    ( ! [X26,X27] : (~r2_orders_2(sK0,X27,sK4(sK0,X26,X27)) | r2_hidden(X27,a_2_1_orders_2(sK0,X26)) | ~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X27,u1_struct_0(sK0))) ) | ~spl7_20),
% 1.67/0.59    inference(avatar_component_clause,[],[f507])).
% 1.67/0.59  fof(f608,plain,(
% 1.67/0.59    ~spl7_2 | spl7_3),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f601])).
% 1.67/0.59  fof(f601,plain,(
% 1.67/0.59    $false | (~spl7_2 | spl7_3)),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f187,f189,f169,f55])).
% 1.67/0.59  fof(f189,plain,(
% 1.67/0.59    m1_subset_1(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | ~spl7_2),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f79,f140,f42])).
% 1.67/0.59  fof(f140,plain,(
% 1.67/0.59    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_orders_2(sK0,k2_tarski(sK2,sK2)))) | ~spl7_2),
% 1.67/0.59    inference(backward_demodulation,[],[f125,f136])).
% 1.67/0.59  fof(f136,plain,(
% 1.67/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f35,f130,f71])).
% 1.67/0.59  fof(f71,plain,(
% 1.67/0.59    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 1.67/0.59    inference(definition_unfolding,[],[f44,f54])).
% 1.67/0.59  fof(f44,plain,(
% 1.67/0.59    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f22])).
% 1.67/0.59  fof(f22,plain,(
% 1.67/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.67/0.59    inference(flattening,[],[f21])).
% 1.67/0.59  fof(f21,plain,(
% 1.67/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f9])).
% 1.67/0.59  fof(f9,axiom,(
% 1.67/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.67/0.59  fof(f125,plain,(
% 1.67/0.59    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))) | ~spl7_2),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f105,f72])).
% 1.67/0.59  fof(f105,plain,(
% 1.67/0.59    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~spl7_2),
% 1.67/0.59    inference(avatar_component_clause,[],[f103])).
% 1.67/0.59  fof(f103,plain,(
% 1.67/0.59    spl7_2 <=> r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.67/0.59  fof(f79,plain,(
% 1.67/0.59    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 1.67/0.59    inference(equality_resolution,[],[f78])).
% 1.67/0.59  fof(f78,plain,(
% 1.67/0.59    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 1.67/0.59    inference(equality_resolution,[],[f69])).
% 1.67/0.59  fof(f69,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.67/0.59    inference(cnf_transformation,[],[f1])).
% 1.67/0.59  fof(f187,plain,(
% 1.67/0.59    ~v1_xboole_0(k2_orders_2(sK0,k2_tarski(sK2,sK2))) | ~spl7_2),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f77,f140,f52])).
% 1.67/0.59  fof(f592,plain,(
% 1.67/0.59    spl7_1 | ~spl7_2 | ~spl7_18 | ~spl7_21),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f585])).
% 1.67/0.59  fof(f585,plain,(
% 1.67/0.59    $false | (spl7_1 | ~spl7_2 | ~spl7_18 | ~spl7_21)),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f187,f189,f570,f55])).
% 1.67/0.59  fof(f570,plain,(
% 1.67/0.59    ~r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | (spl7_1 | ~spl7_18 | ~spl7_21)),
% 1.67/0.59    inference(forward_demodulation,[],[f567,f149])).
% 1.67/0.59  fof(f567,plain,(
% 1.67/0.59    ~r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) | (spl7_1 | ~spl7_18 | ~spl7_21)),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f100,f35,f79,f143,f564])).
% 1.67/0.59  fof(f564,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X0,X2) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1)) ) | (~spl7_18 | ~spl7_21)),
% 1.67/0.59    inference(duplicate_literal_removal,[],[f563])).
% 1.67/0.59  fof(f563,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X0,X2) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_18 | ~spl7_21)),
% 1.67/0.59    inference(superposition,[],[f538,f443])).
% 1.67/0.59  fof(f443,plain,(
% 1.67/0.59    ( ! [X4,X5] : (sK3(X5,sK0,X4) = X5 | ~r2_hidden(X5,a_2_1_orders_2(sK0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_18),
% 1.67/0.59    inference(avatar_component_clause,[],[f442])).
% 1.67/0.59  fof(f442,plain,(
% 1.67/0.59    spl7_18 <=> ! [X5,X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,a_2_1_orders_2(sK0,X4)) | sK3(X5,sK0,X4) = X5)),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.67/0.59  fof(f538,plain,(
% 1.67/0.59    ( ! [X2,X3,X1] : (r2_orders_2(sK0,sK3(X3,sK0,X1),X2) | ~r2_hidden(X3,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1)) ) | ~spl7_21),
% 1.67/0.59    inference(avatar_component_clause,[],[f537])).
% 1.67/0.59  fof(f537,plain,(
% 1.67/0.59    spl7_21 <=> ! [X1,X3,X2] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X3,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X3,sK0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1))),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.67/0.59  fof(f100,plain,(
% 1.67/0.59    ~r2_orders_2(sK0,sK1,sK2) | spl7_1),
% 1.67/0.59    inference(avatar_component_clause,[],[f99])).
% 1.67/0.59  fof(f539,plain,(
% 1.67/0.59    spl7_21 | spl7_5 | ~spl7_8 | ~spl7_9 | ~spl7_6),
% 1.67/0.59    inference(avatar_split_clause,[],[f82,f213,f236,f232,f209,f537])).
% 1.67/0.59  fof(f209,plain,(
% 1.67/0.59    spl7_5 <=> v2_struct_0(sK0)),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.67/0.59  fof(f232,plain,(
% 1.67/0.59    spl7_8 <=> v5_orders_2(sK0)),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.67/0.59  fof(f236,plain,(
% 1.67/0.59    spl7_9 <=> v4_orders_2(sK0)),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.67/0.59  fof(f213,plain,(
% 1.67/0.59    spl7_6 <=> v3_orders_2(sK0)),
% 1.67/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.67/0.59  fof(f82,plain,(
% 1.67/0.59    ( ! [X2,X3,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | r2_orders_2(sK0,sK3(X3,sK0,X1),X2) | ~r2_hidden(X3,a_2_1_orders_2(sK0,X1))) )),
% 1.67/0.59    inference(resolution,[],[f41,f48])).
% 1.67/0.59  fof(f48,plain,(
% 1.67/0.59    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | r2_orders_2(X1,sK3(X0,X1,X2),X4) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f24])).
% 1.67/0.59  fof(f24,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.67/0.59    inference(flattening,[],[f23])).
% 1.67/0.59  fof(f23,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.67/0.59    inference(ennf_transformation,[],[f8])).
% 1.67/0.59  fof(f8,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.67/0.59  fof(f509,plain,(
% 1.67/0.59    spl7_20 | spl7_5 | ~spl7_8 | ~spl7_9 | ~spl7_6),
% 1.67/0.59    inference(avatar_split_clause,[],[f94,f213,f236,f232,f209,f507])).
% 1.67/0.59  fof(f94,plain,(
% 1.67/0.59    ( ! [X26,X27] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X27,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X27,sK4(sK0,X26,X27)) | r2_hidden(X27,a_2_1_orders_2(sK0,X26))) )),
% 1.67/0.59    inference(resolution,[],[f41,f73])).
% 1.67/0.59  fof(f73,plain,(
% 1.67/0.59    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_orders_2(X1,X3,sK4(X1,X2,X3)) | r2_hidden(X3,a_2_1_orders_2(X1,X2))) )),
% 1.67/0.59    inference(equality_resolution,[],[f47])).
% 1.67/0.59  fof(f47,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | ~r2_orders_2(X1,X3,sK4(X1,X2,X3)) | r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f24])).
% 1.67/0.59  fof(f470,plain,(
% 1.67/0.59    spl7_19 | spl7_5 | ~spl7_8 | ~spl7_9 | ~spl7_6),
% 1.67/0.59    inference(avatar_split_clause,[],[f95,f213,f236,f232,f209,f468])).
% 1.67/0.59  fof(f95,plain,(
% 1.67/0.59    ( ! [X28,X29] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X29,u1_struct_0(sK0)) | r2_hidden(sK4(sK0,X28,X29),X28) | r2_hidden(X29,a_2_1_orders_2(sK0,X28))) )),
% 1.67/0.59    inference(resolution,[],[f41,f74])).
% 1.67/0.59  fof(f74,plain,(
% 1.67/0.59    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(sK4(X1,X2,X3),X2) | r2_hidden(X3,a_2_1_orders_2(X1,X2))) )),
% 1.67/0.59    inference(equality_resolution,[],[f46])).
% 1.67/0.59  fof(f46,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | r2_hidden(sK4(X1,X2,X3),X2) | r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f24])).
% 1.67/0.59  fof(f444,plain,(
% 1.67/0.59    spl7_18 | spl7_5 | ~spl7_8 | ~spl7_9 | ~spl7_6),
% 1.67/0.59    inference(avatar_split_clause,[],[f83,f213,f236,f232,f209,f442])).
% 1.67/0.59  fof(f83,plain,(
% 1.67/0.59    ( ! [X4,X5] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X5,sK0,X4) = X5 | ~r2_hidden(X5,a_2_1_orders_2(sK0,X4))) )),
% 1.67/0.59    inference(resolution,[],[f41,f50])).
% 1.67/0.59  fof(f50,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f24])).
% 1.67/0.59  fof(f251,plain,(
% 1.67/0.59    ~spl7_5),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f248])).
% 1.67/0.59  fof(f248,plain,(
% 1.67/0.59    $false | ~spl7_5),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f37,f211])).
% 1.67/0.59  fof(f211,plain,(
% 1.67/0.59    v2_struct_0(sK0) | ~spl7_5),
% 1.67/0.59    inference(avatar_component_clause,[],[f209])).
% 1.67/0.59  fof(f247,plain,(
% 1.67/0.59    spl7_9),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f244])).
% 1.67/0.59  fof(f244,plain,(
% 1.67/0.59    $false | spl7_9),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f39,f238])).
% 1.67/0.59  fof(f238,plain,(
% 1.67/0.59    ~v4_orders_2(sK0) | spl7_9),
% 1.67/0.59    inference(avatar_component_clause,[],[f236])).
% 1.67/0.59  fof(f243,plain,(
% 1.67/0.59    spl7_8),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f240])).
% 1.67/0.59  fof(f240,plain,(
% 1.67/0.59    $false | spl7_8),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f40,f234])).
% 1.67/0.59  fof(f234,plain,(
% 1.67/0.59    ~v5_orders_2(sK0) | spl7_8),
% 1.67/0.59    inference(avatar_component_clause,[],[f232])).
% 1.67/0.59  fof(f220,plain,(
% 1.67/0.59    spl7_6),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f217])).
% 1.67/0.59  fof(f217,plain,(
% 1.67/0.59    $false | spl7_6),
% 1.67/0.59    inference(unit_resulting_resolution,[],[f38,f215])).
% 1.67/0.59  fof(f215,plain,(
% 1.67/0.59    ~v3_orders_2(sK0) | spl7_6),
% 1.67/0.59    inference(avatar_component_clause,[],[f213])).
% 1.67/0.59  fof(f170,plain,(
% 1.67/0.59    ~spl7_1 | ~spl7_3),
% 1.67/0.59    inference(avatar_split_clause,[],[f142,f167,f99])).
% 1.67/0.59  fof(f142,plain,(
% 1.67/0.59    ~r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.67/0.59    inference(backward_demodulation,[],[f34,f136])).
% 1.67/0.59  fof(f34,plain,(
% 1.67/0.59    ~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  fof(f106,plain,(
% 1.67/0.59    spl7_1 | spl7_2),
% 1.67/0.59    inference(avatar_split_clause,[],[f33,f103,f99])).
% 1.67/0.59  fof(f33,plain,(
% 1.67/0.59    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)),
% 1.67/0.59    inference(cnf_transformation,[],[f16])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (18706)------------------------------
% 1.67/0.59  % (18706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (18706)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.59  % (18706)Memory used [KB]: 6780
% 1.67/0.59  % (18706)Time elapsed: 0.175 s
% 1.67/0.59  % (18706)------------------------------
% 1.67/0.59  % (18706)------------------------------
% 1.67/0.60  % (18685)Refutation not found, incomplete strategy% (18685)------------------------------
% 1.67/0.60  % (18685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (18685)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.60  
% 1.67/0.60  % (18685)Memory used [KB]: 2302
% 1.67/0.60  % (18685)Time elapsed: 0.199 s
% 1.67/0.60  % (18685)------------------------------
% 1.67/0.60  % (18685)------------------------------
% 1.67/0.61  % (18680)Success in time 0.244 s
%------------------------------------------------------------------------------
