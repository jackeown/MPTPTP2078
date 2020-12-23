%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2050+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:05 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  152 (1593 expanded)
%              Number of leaves         :   28 ( 618 expanded)
%              Depth                    :   28
%              Number of atoms          : 1122 (12769 expanded)
%              Number of equality atoms :  117 ( 301 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f536,plain,(
    $false ),
    inference(subsumption_resolution,[],[f497,f84])).

fof(f84,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f497,plain,(
    ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f137,f490])).

fof(f490,plain,(
    o_0_0_xboole_0 = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f168,f170,f243,f408])).

fof(f408,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f407,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f407,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f406,f78])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    & m1_yellow19(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f58,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_waybel_0(X0,X1,X2)
                & m1_yellow19(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(sK0,X1,X2)
              & m1_yellow19(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_waybel_0(sK0,X1,X2)
            & m1_yellow19(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_waybel_0(sK0,sK1,X2)
          & m1_yellow19(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X2] :
        ( ~ r1_waybel_0(sK0,sK1,X2)
        & m1_yellow19(X2,sK0,sK1) )
   => ( ~ r1_waybel_0(sK0,sK1,sK2)
      & m1_yellow19(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_yellow19(X2,X0,X1)
               => r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_yellow19(X2,X0,X1)
             => r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow19)).

fof(f406,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f405,f80])).

fof(f80,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f405,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f404,f81])).

fof(f81,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f404,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f403,f143])).

fof(f143,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f81,f82,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f99,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_yellow19(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_yellow19(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow19(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow19)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK6(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK6(X0,X1,X2)))) = X2
                    & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f68,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK6(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK6(X0,X1,X2)))) = X2
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X4] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow19)).

fof(f82,plain,(
    m1_yellow19(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f403,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f402,f336])).

fof(f336,plain,(
    ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f243,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f402,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f401,f76])).

fof(f401,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f400,f77])).

fof(f400,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f399,f230])).

fof(f230,plain,(
    ~ v2_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f79,f80,f81,f216,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f216,plain,(
    m2_yellow_6(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f79,f80,f81,f143,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f120,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_waybel_9)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_9)).

fof(f79,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f399,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | v2_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f398,f220])).

fof(f220,plain,(
    v1_funct_2(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f175,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f175,plain,(
    l1_waybel_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f81,f143,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f398,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ v1_funct_2(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | v2_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f392,f221])).

fof(f221,plain,(
    m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f77,f175,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f392,plain,(
    ! [X4] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X4),sK2)
      | o_0_0_xboole_0 = u1_struct_0(sK0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(sK0))))
      | ~ v1_funct_2(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | v2_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f296,f177])).

fof(f177,plain,(
    sK2 = k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2))),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f81,f82,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK6(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK6(X0,X1,X2)))) = X2
      | ~ m1_yellow19(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f100,f113])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK6(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK6(X0,X1,X2)))) = X2
      | ~ m1_yellow19(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f296,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relset_1(X4,X5,u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | o_0_0_xboole_0 = X5
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f295,f122])).

fof(f295,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relset_1(X4,X5,u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | o_0_0_xboole_0 = X5
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f291])).

fof(f291,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relset_1(X4,X5,u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | o_0_0_xboole_0 = X5
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f218,f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X4) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
                     => ( X3 = X4
                       => k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_waybel_9)).

fof(f218,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X2),k2_relset_1(X3,X4,u1_waybel_0(X0,X1)))
      | o_0_0_xboole_0 = X4
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(u1_waybel_0(X0,X1),X3,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f217,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f217,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X2),k2_relset_1(X3,X4,u1_waybel_0(X0,X1)))
      | o_0_0_xboole_0 = X4
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(u1_waybel_0(X0,X1),X3,X4)
      | ~ v1_funct_1(u1_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(superposition,[],[f125,f154])).

fof(f154,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f153,f114])).

fof(f153,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f152,f115])).

fof(f152,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f151,f116])).

fof(f151,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(u1_waybel_0(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(u1_waybel_0(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(superposition,[],[f88,f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f124,f85])).

fof(f85,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f243,plain,(
    r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK6(sK0,sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f81,f143,f168,f169,f180])).

fof(f180,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f179,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f179,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f131,f122])).

fof(f131,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | X7 != X8
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ( ( ! [X5] :
                              ( ~ r1_orders_2(X1,X2,X5)
                              | sK3(X1,X2,X3) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                          | ~ r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) )
                        & ( ( r1_orders_2(X1,X2,sK4(X1,X2,X3))
                            & sK3(X1,X2,X3) = sK4(X1,X2,X3)
                            & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) )
                          | r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ( r1_orders_2(X1,X2,sK5(X1,X2,X7))
                                & sK5(X1,X2,X7) = X7
                                & m1_subset_1(sK5(X1,X2,X7),u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f62,f65,f64,f63])).

fof(f63,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X2,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X3)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X2,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X3)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X2,X5)
              | sK3(X1,X2,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X2,X6)
              & sK3(X1,X2,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X3,X2,X1] :
      ( ? [X6] :
          ( r1_orders_2(X1,X2,X6)
          & sK3(X1,X2,X3) = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK4(X1,X2,X3))
        & sK3(X1,X2,X3) = sK4(X1,X2,X3)
        & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X7,X2,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X2,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK5(X1,X2,X7))
        & sK5(X1,X2,X7) = X7
        & m1_subset_1(sK5(X1,X2,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X6] :
                                ( r1_orders_2(X1,X2,X6)
                                & X4 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ? [X9] :
                                  ( r1_orders_2(X1,X2,X9)
                                  & X7 = X9
                                  & m1_subset_1(X9,u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f169,plain,(
    r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f81,f83,f143,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK7(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK7(X0,X1,X2,X3))
                      & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f72,f74,f73])).

fof(f73,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f83,plain,(
    ~ r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f170,plain,(
    ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2))),sK2) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f81,f83,f143,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f168,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f76,f77,f78,f81,f83,f143,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f137,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f76,f77,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

%------------------------------------------------------------------------------
