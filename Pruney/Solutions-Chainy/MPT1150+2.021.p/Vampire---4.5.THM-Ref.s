%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:46 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  191 (1405 expanded)
%              Number of leaves         :   28 ( 363 expanded)
%              Depth                    :   27
%              Number of atoms          :  821 (6987 expanded)
%              Number of equality atoms :   78 (1112 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f166,f186,f687,f700,f713,f1113,f1139])).

fof(f1139,plain,(
    ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1138])).

fof(f1138,plain,
    ( $false
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1136,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1136,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))))
    | ~ spl6_28 ),
    inference(resolution,[],[f712,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f712,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f710])).

fof(f710,plain,
    ( spl6_28
  <=> r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1113,plain,
    ( ~ spl6_3
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f1112])).

fof(f1112,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1111,f682])).

fof(f682,plain,
    ( m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f680])).

fof(f680,plain,
    ( spl6_25
  <=> m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1111,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f1110,f108])).

fof(f108,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f102,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f102,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f64,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f64,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f1110,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1109,f63])).

fof(f63,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f1109,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1108,f64])).

fof(f1108,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f1106,f719])).

fof(f719,plain,
    ( r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl6_27 ),
    inference(resolution,[],[f708,f540])).

fof(f540,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f539,f287])).

fof(f287,plain,(
    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f285,f65])).

fof(f65,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f285,plain,
    ( sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f224,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f224,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f220,f203])).

fof(f203,plain,(
    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f125,f110])).

fof(f110,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f107,f108])).

fof(f107,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f102,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f124,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f61])).

fof(f61,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f62])).

fof(f62,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f63])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f64])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f75,f108])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f220,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(resolution,[],[f135,f110])).

fof(f135,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | sK4(X4,sK0,X3) = X4 ) ),
    inference(subsumption_resolution,[],[f134,f60])).

fof(f134,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | sK4(X4,sK0,X3) = X4
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f133,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | sK4(X4,sK0,X3) = X4
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f62])).

fof(f132,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | sK4(X4,sK0,X3) = X4
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f63])).

fof(f131,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | sK4(X4,sK0,X3) = X4
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f64])).

fof(f115,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | sK4(X4,sK0,X3) = X4
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f87,f108])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | sK4(X0,X1,X2) = X0
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).

fof(f56,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f539,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f535,f65])).

fof(f535,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))
      | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f253,f77])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK4(X1,sK0,k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f249,f203])).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK4(X1,sK0,k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f141,f110])).

fof(f141,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X6,X5)
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X5))
      | r2_orders_2(sK0,X6,sK4(X7,sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f140,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

% (1427)Refutation not found, incomplete strategy% (1427)------------------------------
% (1427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1427)Termination reason: Refutation not found, incomplete strategy

% (1427)Memory used [KB]: 10618
% (1427)Time elapsed: 0.098 s
% (1427)------------------------------
% (1427)------------------------------
fof(f140,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X5))
      | r2_orders_2(sK0,X6,sK4(X7,sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f139,f60])).

fof(f139,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X5))
      | r2_orders_2(sK0,X6,sK4(X7,sK0,X5))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f61])).

fof(f138,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X5))
      | r2_orders_2(sK0,X6,sK4(X7,sK0,X5))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f62])).

fof(f137,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X5))
      | r2_orders_2(sK0,X6,sK4(X7,sK0,X5))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f63])).

fof(f136,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X5))
      | r2_orders_2(sK0,X6,sK4(X7,sK0,X5))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f64])).

fof(f116,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,k2_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X5))
      | r2_orders_2(sK0,X6,sK4(X7,sK0,X5))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f88,f108])).

fof(f88,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_orders_2(X1,X6,sK4(X0,X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f708,plain,
    ( r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f706])).

fof(f706,plain,
    ( spl6_27
  <=> r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1106,plain,
    ( ~ r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(duplicate_literal_removal,[],[f1105])).

fof(f1105,plain,
    ( ~ r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(resolution,[],[f1093,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

% (1428)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

fof(f1093,plain,
    ( r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1092,f682])).

fof(f1092,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f1091,f108])).

fof(f1091,plain,
    ( r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1090,f60])).

fof(f1090,plain,
    ( r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1089,f61])).

fof(f1089,plain,
    ( r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1088,f64])).

fof(f1088,plain,
    ( r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(duplicate_literal_removal,[],[f1087])).

fof(f1087,plain,
    ( r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(resolution,[],[f704,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f704,plain,
    ( r3_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(resolution,[],[f682,f165])).

fof(f165,plain,
    ( ! [X13] :
        ( ~ m1_subset_1(X13,k2_struct_0(sK0))
        | r3_orders_2(sK0,X13,X13) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_3
  <=> ! [X13] :
        ( ~ m1_subset_1(X13,k2_struct_0(sK0))
        | r3_orders_2(sK0,X13,X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

% (1428)Refutation not found, incomplete strategy% (1428)------------------------------
% (1428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1428)Termination reason: Refutation not found, incomplete strategy

% (1428)Memory used [KB]: 10618
% (1428)Time elapsed: 0.139 s
% (1428)------------------------------
% (1428)------------------------------
fof(f713,plain,
    ( spl6_27
    | spl6_28
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f703,f680,f710,f706])).

fof(f703,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0)
    | r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl6_25 ),
    inference(resolution,[],[f682,f273])).

fof(f273,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | r2_hidden(sK3(sK0,k1_xboole_0,X1),k1_xboole_0)
      | r2_hidden(X1,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f269,f207])).

fof(f207,plain,(
    k2_struct_0(sK0) = a_2_0_orders_2(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f204,f112])).

fof(f112,plain,(
    k2_struct_0(sK0) = k1_orders_2(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f111,f109])).

fof(f109,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f102,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f111,plain,(
    k2_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f106,f108])).

fof(f106,plain,(
    u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f105,f60])).

fof(f105,plain,
    ( u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f61])).

fof(f104,plain,
    ( u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f62])).

fof(f103,plain,
    ( u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f63])).

fof(f101,plain,
    ( u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

% (1445)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

fof(f204,plain,(
    k1_orders_2(sK0,k1_xboole_0) = a_2_0_orders_2(sK0,k1_xboole_0) ),
    inference(resolution,[],[f125,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f269,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k1_xboole_0,X1),k1_xboole_0)
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | r2_hidden(X1,a_2_0_orders_2(sK0,k1_xboole_0)) ) ),
    inference(resolution,[],[f146,f68])).

fof(f146,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X8,X9),X8)
      | ~ m1_subset_1(X9,k2_struct_0(sK0))
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) ) ),
    inference(subsumption_resolution,[],[f145,f60])).

fof(f145,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X8,X9),X8)
      | ~ m1_subset_1(X9,k2_struct_0(sK0))
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f61])).

fof(f144,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X8,X9),X8)
      | ~ m1_subset_1(X9,k2_struct_0(sK0))
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f62])).

fof(f143,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X8,X9),X8)
      | ~ m1_subset_1(X9,k2_struct_0(sK0))
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f63])).

% (1435)Refutation not found, incomplete strategy% (1435)------------------------------
% (1435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1435)Termination reason: Refutation not found, incomplete strategy

% (1435)Memory used [KB]: 10618
% (1435)Time elapsed: 0.139 s
% (1435)------------------------------
% (1435)------------------------------
fof(f142,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X8,X9),X8)
      | ~ m1_subset_1(X9,k2_struct_0(sK0))
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f64])).

fof(f117,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X8,X9),X8)
      | ~ m1_subset_1(X9,k2_struct_0(sK0))
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f97,f108])).

fof(f97,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f700,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | spl6_26 ),
    inference(subsumption_resolution,[],[f698,f65])).

fof(f698,plain,
    ( k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))
    | spl6_26 ),
    inference(resolution,[],[f686,f77])).

fof(f686,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0)))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f684])).

fof(f684,plain,
    ( spl6_26
  <=> r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f687,plain,
    ( spl6_25
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f678,f684,f680])).

fof(f678,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0)))
    | m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f677,f203])).

fof(f677,plain,
    ( m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),a_2_0_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f676,f110])).

fof(f676,plain,
    ( m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),a_2_0_orders_2(sK0,k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f130,f287])).

fof(f130,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f129,f60])).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f61])).

fof(f128,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f62])).

fof(f127,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f63])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f114,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f86,f108])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f186,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f175,f172])).

fof(f172,plain,
    ( k1_xboole_0 != k1_orders_2(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f65,f170])).

fof(f170,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f169,f77])).

fof(f169,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_struct_0(sK0))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f167,f158])).

fof(f158,plain,
    ( ! [X12] : ~ m1_subset_1(X12,k2_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_2
  <=> ! [X12] : ~ m1_subset_1(X12,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f167,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f110,f95])).

fof(f175,plain,
    ( k1_xboole_0 = k1_orders_2(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f112,f170])).

fof(f166,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f162,f164,f153])).

fof(f153,plain,
    ( spl6_1
  <=> sP5(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f162,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | r3_orders_2(sK0,X13,X13)
      | ~ sP5(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f60])).

fof(f161,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | r3_orders_2(sK0,X13,X13)
      | v2_struct_0(sK0)
      | ~ sP5(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f61])).

fof(f160,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | r3_orders_2(sK0,X13,X13)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ sP5(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f64])).

fof(f120,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k2_struct_0(sK0))
      | r3_orders_2(sK0,X13,X13)
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ sP5(sK0) ) ),
    inference(superposition,[],[f100,f108])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP5(X0) ) ),
    inference(general_splitting,[],[f92,f99_D])).

fof(f99,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f99_D])).

fof(f99_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f159,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f119,f157,f153])).

fof(f119,plain,(
    ! [X12] :
      ( ~ m1_subset_1(X12,k2_struct_0(sK0))
      | sP5(sK0) ) ),
    inference(superposition,[],[f99,f108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (1423)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (1447)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (1439)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (1426)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (1424)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (1425)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (1422)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1440)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (1429)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (1430)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1440)Refutation not found, incomplete strategy% (1440)------------------------------
% 0.21/0.53  % (1440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1420)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (1440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1440)Memory used [KB]: 10746
% 0.21/0.53  % (1440)Time elapsed: 0.120 s
% 0.21/0.53  % (1440)------------------------------
% 0.21/0.53  % (1440)------------------------------
% 0.21/0.54  % (1443)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (1429)Refutation not found, incomplete strategy% (1429)------------------------------
% 0.21/0.54  % (1429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1429)Memory used [KB]: 10618
% 0.21/0.54  % (1429)Time elapsed: 0.126 s
% 0.21/0.54  % (1429)------------------------------
% 0.21/0.54  % (1429)------------------------------
% 0.21/0.54  % (1431)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (1434)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (1419)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1427)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (1446)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (1441)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (1433)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (1435)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (1421)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (1436)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  % (1426)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (1444)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  % (1438)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f1141,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f159,f166,f186,f687,f700,f713,f1113,f1139])).
% 1.32/0.55  fof(f1139,plain,(
% 1.32/0.55    ~spl6_28),
% 1.32/0.55    inference(avatar_contradiction_clause,[],[f1138])).
% 1.32/0.55  fof(f1138,plain,(
% 1.32/0.55    $false | ~spl6_28),
% 1.32/0.55    inference(subsumption_resolution,[],[f1136,f66])).
% 1.32/0.55  fof(f66,plain,(
% 1.32/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.32/0.55  fof(f1136,plain,(
% 1.32/0.55    ~r1_tarski(k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))))) | ~spl6_28),
% 1.32/0.55    inference(resolution,[],[f712,f85])).
% 1.32/0.55  fof(f85,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f36])).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.32/0.55    inference(ennf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,axiom,(
% 1.32/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.32/0.55  fof(f712,plain,(
% 1.32/0.55    r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0) | ~spl6_28),
% 1.32/0.55    inference(avatar_component_clause,[],[f710])).
% 1.32/0.55  fof(f710,plain,(
% 1.32/0.55    spl6_28 <=> r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0)),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.32/0.55  fof(f1113,plain,(
% 1.32/0.55    ~spl6_3 | ~spl6_25 | ~spl6_27),
% 1.32/0.55    inference(avatar_contradiction_clause,[],[f1112])).
% 1.32/0.55  fof(f1112,plain,(
% 1.32/0.55    $false | (~spl6_3 | ~spl6_25 | ~spl6_27)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1111,f682])).
% 1.32/0.55  fof(f682,plain,(
% 1.32/0.55    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl6_25),
% 1.32/0.55    inference(avatar_component_clause,[],[f680])).
% 1.32/0.55  fof(f680,plain,(
% 1.32/0.55    spl6_25 <=> m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.32/0.55  fof(f1111,plain,(
% 1.32/0.55    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (~spl6_3 | ~spl6_25 | ~spl6_27)),
% 1.32/0.55    inference(forward_demodulation,[],[f1110,f108])).
% 1.32/0.55  fof(f108,plain,(
% 1.32/0.55    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.32/0.55    inference(resolution,[],[f102,f71])).
% 1.32/0.55  fof(f71,plain,(
% 1.32/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f11])).
% 1.32/0.55  fof(f11,axiom,(
% 1.32/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.32/0.55  fof(f102,plain,(
% 1.32/0.55    l1_struct_0(sK0)),
% 1.32/0.55    inference(resolution,[],[f64,f73])).
% 1.32/0.55  fof(f73,plain,(
% 1.32/0.55    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f27])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f14])).
% 1.32/0.55  fof(f14,axiom,(
% 1.32/0.55    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.32/0.55  fof(f64,plain,(
% 1.32/0.55    l1_orders_2(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f46])).
% 1.32/0.55  fof(f46,plain,(
% 1.32/0.55    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f45])).
% 1.32/0.55  fof(f45,plain,(
% 1.32/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f22])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f21])).
% 1.32/0.55  fof(f21,negated_conjecture,(
% 1.32/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.32/0.55    inference(negated_conjecture,[],[f20])).
% 1.32/0.55  fof(f20,conjecture,(
% 1.32/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).
% 1.32/0.55  fof(f1110,plain,(
% 1.32/0.55    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | (~spl6_3 | ~spl6_25 | ~spl6_27)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1109,f63])).
% 1.32/0.55  fof(f63,plain,(
% 1.32/0.55    v5_orders_2(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f46])).
% 1.32/0.55  fof(f1109,plain,(
% 1.32/0.55    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | (~spl6_3 | ~spl6_25 | ~spl6_27)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1108,f64])).
% 1.32/0.55  fof(f1108,plain,(
% 1.32/0.55    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | (~spl6_3 | ~spl6_25 | ~spl6_27)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1106,f719])).
% 1.32/0.55  fof(f719,plain,(
% 1.32/0.55    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~spl6_27),
% 1.32/0.55    inference(resolution,[],[f708,f540])).
% 1.32/0.55  fof(f540,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))))) )),
% 1.32/0.55    inference(forward_demodulation,[],[f539,f287])).
% 1.32/0.55  fof(f287,plain,(
% 1.32/0.55    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 1.32/0.55    inference(subsumption_resolution,[],[f285,f65])).
% 1.32/0.55  fof(f65,plain,(
% 1.32/0.55    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))),
% 1.32/0.55    inference(cnf_transformation,[],[f46])).
% 1.32/0.55  fof(f285,plain,(
% 1.32/0.55    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 1.32/0.55    inference(resolution,[],[f224,f77])).
% 1.32/0.55  fof(f77,plain,(
% 1.32/0.55    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f48])).
% 1.32/0.55  fof(f48,plain,(
% 1.32/0.55    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f47])).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f34,plain,(
% 1.32/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.32/0.55    inference(ennf_transformation,[],[f9])).
% 1.32/0.55  fof(f9,axiom,(
% 1.32/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.32/0.55  fof(f224,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 1.32/0.55    inference(forward_demodulation,[],[f220,f203])).
% 1.32/0.55  fof(f203,plain,(
% 1.32/0.55    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0))),
% 1.32/0.55    inference(resolution,[],[f125,f110])).
% 1.32/0.55  fof(f110,plain,(
% 1.32/0.55    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.32/0.55    inference(backward_demodulation,[],[f107,f108])).
% 1.32/0.55  fof(f107,plain,(
% 1.32/0.55    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.55    inference(resolution,[],[f102,f72])).
% 1.32/0.55  fof(f72,plain,(
% 1.32/0.55    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f26])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f12])).
% 1.32/0.55  fof(f12,axiom,(
% 1.32/0.55    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 1.32/0.55  fof(f125,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f124,f60])).
% 1.32/0.55  fof(f60,plain,(
% 1.32/0.55    ~v2_struct_0(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f46])).
% 1.32/0.55  fof(f124,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f123,f61])).
% 1.32/0.55  fof(f61,plain,(
% 1.32/0.55    v3_orders_2(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f46])).
% 1.32/0.55  fof(f123,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f122,f62])).
% 1.32/0.55  fof(f62,plain,(
% 1.32/0.55    v4_orders_2(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f46])).
% 1.32/0.55  fof(f122,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f121,f63])).
% 1.32/0.55  fof(f121,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f113,f64])).
% 1.32/0.55  fof(f113,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(superposition,[],[f75,f108])).
% 1.32/0.55  fof(f75,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f31])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f30])).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f13])).
% 1.32/0.55  fof(f13,axiom,(
% 1.32/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 1.32/0.55  fof(f220,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,a_2_0_orders_2(sK0,k2_struct_0(sK0))) | sK4(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 1.32/0.55    inference(resolution,[],[f135,f110])).
% 1.32/0.55  fof(f135,plain,(
% 1.32/0.55    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | sK4(X4,sK0,X3) = X4) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f134,f60])).
% 1.32/0.55  fof(f134,plain,(
% 1.32/0.55    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | sK4(X4,sK0,X3) = X4 | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f133,f61])).
% 1.32/0.55  fof(f133,plain,(
% 1.32/0.55    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | sK4(X4,sK0,X3) = X4 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f132,f62])).
% 1.32/0.55  fof(f132,plain,(
% 1.32/0.55    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | sK4(X4,sK0,X3) = X4 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f131,f63])).
% 1.32/0.55  fof(f131,plain,(
% 1.32/0.55    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | sK4(X4,sK0,X3) = X4 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f115,f64])).
% 1.32/0.55  fof(f115,plain,(
% 1.32/0.55    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | sK4(X4,sK0,X3) = X4 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(superposition,[],[f87,f108])).
% 1.32/0.55  fof(f87,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | sK4(X0,X1,X2) = X0 | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f58])).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).
% 1.32/0.55  fof(f56,plain,(
% 1.32/0.55    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f57,plain,(
% 1.32/0.55    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f55,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.32/0.55    inference(rectify,[],[f54])).
% 1.32/0.55  fof(f54,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.32/0.55    inference(nnf_transformation,[],[f38])).
% 1.32/0.55  fof(f38,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.32/0.55    inference(flattening,[],[f37])).
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f15])).
% 1.32/0.55  fof(f15,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.32/0.55  fof(f539,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f535,f65])).
% 1.32/0.55  fof(f535,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))) )),
% 1.32/0.55    inference(resolution,[],[f253,f77])).
% 1.32/0.55  fof(f253,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK4(X1,sK0,k2_struct_0(sK0)))) )),
% 1.32/0.55    inference(forward_demodulation,[],[f249,f203])).
% 1.32/0.55  fof(f249,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(X1,a_2_0_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X0,sK4(X1,sK0,k2_struct_0(sK0)))) )),
% 1.32/0.55    inference(resolution,[],[f141,f110])).
% 1.32/0.55  fof(f141,plain,(
% 1.32/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X6,X5) | ~r2_hidden(X7,a_2_0_orders_2(sK0,X5)) | r2_orders_2(sK0,X6,sK4(X7,sK0,X5))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f140,f95])).
% 1.32/0.55  fof(f95,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f44])).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.32/0.55    inference(flattening,[],[f43])).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f7])).
% 1.32/0.55  fof(f7,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.32/0.55  % (1427)Refutation not found, incomplete strategy% (1427)------------------------------
% 1.32/0.55  % (1427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (1427)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (1427)Memory used [KB]: 10618
% 1.32/0.55  % (1427)Time elapsed: 0.098 s
% 1.32/0.55  % (1427)------------------------------
% 1.32/0.55  % (1427)------------------------------
% 1.32/0.55  fof(f140,plain,(
% 1.32/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~r2_hidden(X7,a_2_0_orders_2(sK0,X5)) | r2_orders_2(sK0,X6,sK4(X7,sK0,X5))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f139,f60])).
% 1.32/0.55  fof(f139,plain,(
% 1.32/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~r2_hidden(X7,a_2_0_orders_2(sK0,X5)) | r2_orders_2(sK0,X6,sK4(X7,sK0,X5)) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f138,f61])).
% 1.32/0.55  fof(f138,plain,(
% 1.32/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~r2_hidden(X7,a_2_0_orders_2(sK0,X5)) | r2_orders_2(sK0,X6,sK4(X7,sK0,X5)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f137,f62])).
% 1.32/0.55  fof(f137,plain,(
% 1.32/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~r2_hidden(X7,a_2_0_orders_2(sK0,X5)) | r2_orders_2(sK0,X6,sK4(X7,sK0,X5)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f136,f63])).
% 1.32/0.55  fof(f136,plain,(
% 1.32/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~r2_hidden(X7,a_2_0_orders_2(sK0,X5)) | r2_orders_2(sK0,X6,sK4(X7,sK0,X5)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f116,f64])).
% 1.32/0.55  fof(f116,plain,(
% 1.32/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,k2_struct_0(sK0)) | ~r2_hidden(X7,a_2_0_orders_2(sK0,X5)) | r2_orders_2(sK0,X6,sK4(X7,sK0,X5)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(superposition,[],[f88,f108])).
% 1.32/0.55  fof(f88,plain,(
% 1.32/0.55    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f58])).
% 1.32/0.55  fof(f708,plain,(
% 1.32/0.55    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl6_27),
% 1.32/0.55    inference(avatar_component_clause,[],[f706])).
% 1.32/0.55  fof(f706,plain,(
% 1.32/0.55    spl6_27 <=> r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.32/0.55  fof(f1106,plain,(
% 1.32/0.55    ~r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f1105])).
% 1.32/0.55  fof(f1105,plain,(
% 1.32/0.55    ~r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(resolution,[],[f1093,f76])).
% 1.32/0.55  fof(f76,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f33])).
% 1.32/0.55  % (1428)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.32/0.55    inference(flattening,[],[f32])).
% 1.32/0.55  fof(f32,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f18])).
% 1.32/0.55  fof(f18,axiom,(
% 1.32/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).
% 1.32/0.55  fof(f1093,plain,(
% 1.32/0.55    r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1092,f682])).
% 1.32/0.55  fof(f1092,plain,(
% 1.32/0.55    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(forward_demodulation,[],[f1091,f108])).
% 1.32/0.55  fof(f1091,plain,(
% 1.32/0.55    r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1090,f60])).
% 1.32/0.55  fof(f1090,plain,(
% 1.32/0.55    r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1089,f61])).
% 1.32/0.55  fof(f1089,plain,(
% 1.32/0.55    r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(subsumption_resolution,[],[f1088,f64])).
% 1.32/0.55  fof(f1088,plain,(
% 1.32/0.55    r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f1087])).
% 1.32/0.55  fof(f1087,plain,(
% 1.32/0.55    r1_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(resolution,[],[f704,f93])).
% 1.32/0.55  fof(f93,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f59])).
% 1.32/0.55  fof(f59,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(nnf_transformation,[],[f42])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f41])).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f16])).
% 1.32/0.55  fof(f16,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.32/0.55  fof(f704,plain,(
% 1.32/0.55    r3_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | (~spl6_3 | ~spl6_25)),
% 1.32/0.55    inference(resolution,[],[f682,f165])).
% 1.32/0.55  fof(f165,plain,(
% 1.32/0.55    ( ! [X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | r3_orders_2(sK0,X13,X13)) ) | ~spl6_3),
% 1.32/0.55    inference(avatar_component_clause,[],[f164])).
% 1.32/0.55  fof(f164,plain,(
% 1.32/0.55    spl6_3 <=> ! [X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | r3_orders_2(sK0,X13,X13))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.32/0.55  % (1428)Refutation not found, incomplete strategy% (1428)------------------------------
% 1.32/0.55  % (1428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (1428)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (1428)Memory used [KB]: 10618
% 1.32/0.55  % (1428)Time elapsed: 0.139 s
% 1.32/0.55  % (1428)------------------------------
% 1.32/0.55  % (1428)------------------------------
% 1.32/0.55  fof(f713,plain,(
% 1.32/0.55    spl6_27 | spl6_28 | ~spl6_25),
% 1.32/0.55    inference(avatar_split_clause,[],[f703,f680,f710,f706])).
% 1.32/0.55  fof(f703,plain,(
% 1.32/0.55    r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0) | r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl6_25),
% 1.32/0.55    inference(resolution,[],[f682,f273])).
% 1.32/0.55  fof(f273,plain,(
% 1.32/0.55    ( ! [X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(sK3(sK0,k1_xboole_0,X1),k1_xboole_0) | r2_hidden(X1,k2_struct_0(sK0))) )),
% 1.32/0.55    inference(forward_demodulation,[],[f269,f207])).
% 1.32/0.55  fof(f207,plain,(
% 1.32/0.55    k2_struct_0(sK0) = a_2_0_orders_2(sK0,k1_xboole_0)),
% 1.32/0.55    inference(forward_demodulation,[],[f204,f112])).
% 1.32/0.55  fof(f112,plain,(
% 1.32/0.55    k2_struct_0(sK0) = k1_orders_2(sK0,k1_xboole_0)),
% 1.32/0.55    inference(backward_demodulation,[],[f111,f109])).
% 1.32/0.55  fof(f109,plain,(
% 1.32/0.55    k1_xboole_0 = k1_struct_0(sK0)),
% 1.32/0.55    inference(resolution,[],[f102,f70])).
% 1.32/0.55  fof(f70,plain,(
% 1.32/0.55    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f24])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f10])).
% 1.32/0.55  fof(f10,axiom,(
% 1.32/0.55    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 1.32/0.55  fof(f111,plain,(
% 1.32/0.55    k2_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0))),
% 1.32/0.55    inference(backward_demodulation,[],[f106,f108])).
% 1.32/0.55  fof(f106,plain,(
% 1.32/0.55    u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0))),
% 1.32/0.55    inference(subsumption_resolution,[],[f105,f60])).
% 1.32/0.55  fof(f105,plain,(
% 1.32/0.55    u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f104,f61])).
% 1.32/0.55  fof(f104,plain,(
% 1.32/0.55    u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f103,f62])).
% 1.32/0.55  fof(f103,plain,(
% 1.32/0.55    u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f101,f63])).
% 1.32/0.55  fof(f101,plain,(
% 1.32/0.55    u1_struct_0(sK0) = k1_orders_2(sK0,k1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.32/0.55    inference(resolution,[],[f64,f74])).
% 1.32/0.55  fof(f74,plain,(
% 1.32/0.55    ( ! [X0] : (~l1_orders_2(X0) | u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f29])).
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f28])).
% 1.32/0.55  fof(f28,plain,(
% 1.32/0.55    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f19])).
% 1.32/0.55  % (1445)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  fof(f19,axiom,(
% 1.32/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).
% 1.32/0.55  fof(f204,plain,(
% 1.32/0.55    k1_orders_2(sK0,k1_xboole_0) = a_2_0_orders_2(sK0,k1_xboole_0)),
% 1.32/0.55    inference(resolution,[],[f125,f68])).
% 1.32/0.55  fof(f68,plain,(
% 1.32/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f5])).
% 1.32/0.55  fof(f5,axiom,(
% 1.32/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.32/0.55  fof(f269,plain,(
% 1.32/0.55    ( ! [X1] : (r2_hidden(sK3(sK0,k1_xboole_0,X1),k1_xboole_0) | ~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(X1,a_2_0_orders_2(sK0,k1_xboole_0))) )),
% 1.32/0.55    inference(resolution,[],[f146,f68])).
% 1.32/0.55  fof(f146,plain,(
% 1.32/0.55    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X8,X9),X8) | ~m1_subset_1(X9,k2_struct_0(sK0)) | r2_hidden(X9,a_2_0_orders_2(sK0,X8))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f145,f60])).
% 1.32/0.55  fof(f145,plain,(
% 1.32/0.55    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X8,X9),X8) | ~m1_subset_1(X9,k2_struct_0(sK0)) | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f144,f61])).
% 1.32/0.55  fof(f144,plain,(
% 1.32/0.55    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X8,X9),X8) | ~m1_subset_1(X9,k2_struct_0(sK0)) | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f143,f62])).
% 1.32/0.55  fof(f143,plain,(
% 1.32/0.55    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X8,X9),X8) | ~m1_subset_1(X9,k2_struct_0(sK0)) | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f142,f63])).
% 1.32/0.55  % (1435)Refutation not found, incomplete strategy% (1435)------------------------------
% 1.32/0.55  % (1435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (1435)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (1435)Memory used [KB]: 10618
% 1.32/0.55  % (1435)Time elapsed: 0.139 s
% 1.32/0.55  % (1435)------------------------------
% 1.32/0.55  % (1435)------------------------------
% 1.32/0.56  fof(f142,plain,(
% 1.32/0.56    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X8,X9),X8) | ~m1_subset_1(X9,k2_struct_0(sK0)) | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f117,f64])).
% 1.32/0.56  fof(f117,plain,(
% 1.32/0.56    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X8,X9),X8) | ~m1_subset_1(X9,k2_struct_0(sK0)) | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.56    inference(superposition,[],[f97,f108])).
% 1.32/0.56  fof(f97,plain,(
% 1.32/0.56    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.32/0.56    inference(equality_resolution,[],[f90])).
% 1.32/0.56  fof(f90,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f58])).
% 1.32/0.56  fof(f700,plain,(
% 1.32/0.56    spl6_26),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f699])).
% 1.32/0.56  fof(f699,plain,(
% 1.32/0.56    $false | spl6_26),
% 1.32/0.56    inference(subsumption_resolution,[],[f698,f65])).
% 1.32/0.56  fof(f698,plain,(
% 1.32/0.56    k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) | spl6_26),
% 1.32/0.56    inference(resolution,[],[f686,f77])).
% 1.32/0.56  fof(f686,plain,(
% 1.32/0.56    ~r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0))) | spl6_26),
% 1.32/0.56    inference(avatar_component_clause,[],[f684])).
% 1.32/0.56  fof(f684,plain,(
% 1.32/0.56    spl6_26 <=> r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0)))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.32/0.56  fof(f687,plain,(
% 1.32/0.56    spl6_25 | ~spl6_26),
% 1.32/0.56    inference(avatar_split_clause,[],[f678,f684,f680])).
% 1.32/0.56  fof(f678,plain,(
% 1.32/0.56    ~r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 1.32/0.56    inference(forward_demodulation,[],[f677,f203])).
% 1.32/0.56  fof(f677,plain,(
% 1.32/0.56    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),a_2_0_orders_2(sK0,k2_struct_0(sK0)))),
% 1.32/0.56    inference(subsumption_resolution,[],[f676,f110])).
% 1.32/0.56  fof(f676,plain,(
% 1.32/0.56    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),a_2_0_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.32/0.56    inference(superposition,[],[f130,f287])).
% 1.32/0.56  fof(f130,plain,(
% 1.32/0.56    ( ! [X2,X1] : (m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f129,f60])).
% 1.32/0.56  fof(f129,plain,(
% 1.32/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f128,f61])).
% 1.32/0.56  fof(f128,plain,(
% 1.32/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f127,f62])).
% 1.32/0.56  fof(f127,plain,(
% 1.32/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f126,f63])).
% 1.32/0.56  fof(f126,plain,(
% 1.32/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f114,f64])).
% 1.32/0.56  fof(f114,plain,(
% 1.32/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | m1_subset_1(sK4(X2,sK0,X1),k2_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.32/0.56    inference(superposition,[],[f86,f108])).
% 1.32/0.56  fof(f86,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f58])).
% 1.32/0.56  fof(f186,plain,(
% 1.32/0.56    ~spl6_2),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f185])).
% 1.32/0.56  fof(f185,plain,(
% 1.32/0.56    $false | ~spl6_2),
% 1.32/0.56    inference(subsumption_resolution,[],[f175,f172])).
% 1.32/0.56  fof(f172,plain,(
% 1.32/0.56    k1_xboole_0 != k1_orders_2(sK0,k1_xboole_0) | ~spl6_2),
% 1.32/0.56    inference(backward_demodulation,[],[f65,f170])).
% 1.32/0.56  fof(f170,plain,(
% 1.32/0.56    k1_xboole_0 = k2_struct_0(sK0) | ~spl6_2),
% 1.32/0.56    inference(resolution,[],[f169,f77])).
% 1.32/0.56  fof(f169,plain,(
% 1.32/0.56    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0))) ) | ~spl6_2),
% 1.32/0.56    inference(subsumption_resolution,[],[f167,f158])).
% 1.32/0.56  fof(f158,plain,(
% 1.32/0.56    ( ! [X12] : (~m1_subset_1(X12,k2_struct_0(sK0))) ) | ~spl6_2),
% 1.32/0.56    inference(avatar_component_clause,[],[f157])).
% 1.32/0.56  fof(f157,plain,(
% 1.32/0.56    spl6_2 <=> ! [X12] : ~m1_subset_1(X12,k2_struct_0(sK0))),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.32/0.56  fof(f167,plain,(
% 1.32/0.56    ( ! [X0] : (m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k2_struct_0(sK0))) )),
% 1.32/0.56    inference(resolution,[],[f110,f95])).
% 1.32/0.56  fof(f175,plain,(
% 1.32/0.56    k1_xboole_0 = k1_orders_2(sK0,k1_xboole_0) | ~spl6_2),
% 1.32/0.56    inference(backward_demodulation,[],[f112,f170])).
% 1.32/0.56  fof(f166,plain,(
% 1.32/0.56    ~spl6_1 | spl6_3),
% 1.32/0.56    inference(avatar_split_clause,[],[f162,f164,f153])).
% 1.32/0.56  fof(f153,plain,(
% 1.32/0.56    spl6_1 <=> sP5(sK0)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.32/0.56  fof(f162,plain,(
% 1.32/0.56    ( ! [X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | r3_orders_2(sK0,X13,X13) | ~sP5(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f161,f60])).
% 1.32/0.56  fof(f161,plain,(
% 1.32/0.56    ( ! [X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | r3_orders_2(sK0,X13,X13) | v2_struct_0(sK0) | ~sP5(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f160,f61])).
% 1.32/0.56  fof(f160,plain,(
% 1.32/0.56    ( ! [X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | r3_orders_2(sK0,X13,X13) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~sP5(sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f120,f64])).
% 1.32/0.56  fof(f120,plain,(
% 1.32/0.56    ( ! [X13] : (~m1_subset_1(X13,k2_struct_0(sK0)) | r3_orders_2(sK0,X13,X13) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~sP5(sK0)) )),
% 1.32/0.56    inference(superposition,[],[f100,f108])).
% 1.32/0.56  fof(f100,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~sP5(X0)) )),
% 1.32/0.56    inference(general_splitting,[],[f92,f99_D])).
% 1.32/0.56  fof(f99,plain,(
% 1.32/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP5(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f99_D])).
% 1.32/0.56  fof(f99_D,plain,(
% 1.32/0.56    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,u1_struct_0(X0)) ) <=> ~sP5(X0)) )),
% 1.32/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.32/0.56  fof(f92,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f40])).
% 1.32/0.56  fof(f40,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.32/0.56    inference(flattening,[],[f39])).
% 1.32/0.56  fof(f39,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f17])).
% 1.32/0.56  fof(f17,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 1.32/0.56  fof(f159,plain,(
% 1.32/0.56    spl6_1 | spl6_2),
% 1.32/0.56    inference(avatar_split_clause,[],[f119,f157,f153])).
% 1.32/0.56  fof(f119,plain,(
% 1.32/0.56    ( ! [X12] : (~m1_subset_1(X12,k2_struct_0(sK0)) | sP5(sK0)) )),
% 1.32/0.56    inference(superposition,[],[f99,f108])).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (1426)------------------------------
% 1.32/0.56  % (1426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (1426)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (1426)Memory used [KB]: 11257
% 1.32/0.56  % (1426)Time elapsed: 0.122 s
% 1.32/0.56  % (1426)------------------------------
% 1.32/0.56  % (1426)------------------------------
% 1.32/0.56  % (1417)Success in time 0.196 s
%------------------------------------------------------------------------------
