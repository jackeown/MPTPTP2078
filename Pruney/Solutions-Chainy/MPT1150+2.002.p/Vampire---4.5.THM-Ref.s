%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:43 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 757 expanded)
%              Number of leaves         :   22 ( 188 expanded)
%              Depth                    :   30
%              Number of atoms          :  697 (3970 expanded)
%              Number of equality atoms :   80 ( 629 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f417,f728,f1102])).

fof(f1102,plain,
    ( ~ spl5_12
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f1101])).

fof(f1101,plain,
    ( $false
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1100,f380])).

fof(f380,plain,
    ( m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl5_12
  <=> m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1100,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_12
    | spl5_15 ),
    inference(forward_demodulation,[],[f1099,f93])).

fof(f93,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f92,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f55,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f33])).

fof(f33,plain,
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

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

fof(f1099,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1096,f55])).

fof(f1096,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl5_12
    | spl5_15 ),
    inference(resolution,[],[f1084,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f1084,plain,
    ( r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f1073,f720])).

fof(f720,plain,(
    r1_tarski(k1_orders_2(sK0,k1_xboole_0),k2_struct_0(sK0)) ),
    inference(resolution,[],[f141,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f141,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_orders_2(sK0,X3),k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f110,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f110,plain,(
    ! [X1] :
      ( m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f109,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f55])).

fof(f95,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f68,f93])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f1073,plain,
    ( ~ r1_tarski(k1_orders_2(sK0,k1_xboole_0),k2_struct_0(sK0))
    | r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl5_12
    | spl5_15 ),
    inference(resolution,[],[f801,f364])).

fof(f364,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,k2_struct_0(sK0))
      | r2_orders_2(sK0,X10,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f363,f56])).

fof(f56,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f363,plain,(
    ! [X10] :
      ( k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))
      | r2_orders_2(sK0,X10,sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X10,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f362,f143])).

fof(f143,plain,(
    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f138,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f138,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f105,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f103,f52])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f53])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f54])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f55])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f64,f93])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f362,plain,(
    ! [X10] :
      ( r2_orders_2(sK0,X10,sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X10,k2_struct_0(sK0))
      | k1_xboole_0 = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f361,f226])).

fof(f226,plain,(
    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f224,f56])).

fof(f224,plain,
    ( sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f223,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f223,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(subsumption_resolution,[],[f221,f87])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X0,sK0,k2_struct_0(sK0)) = X0
      | ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) ) ),
    inference(superposition,[],[f146,f143])).

fof(f146,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,X2))
      | sK4(X1,sK0,X2) = X1
      | ~ r1_tarski(X2,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f120,f76])).

fof(f120,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X5,a_2_0_orders_2(sK0,X4))
      | sK4(X5,sK0,X4) = X5 ) ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f119,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X5,a_2_0_orders_2(sK0,X4))
      | sK4(X5,sK0,X4) = X5
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f52])).

fof(f118,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X5,a_2_0_orders_2(sK0,X4))
      | sK4(X5,sK0,X4) = X5
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f53])).

fof(f117,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X5,a_2_0_orders_2(sK0,X4))
      | sK4(X5,sK0,X4) = X5
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f54])).

fof(f116,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X5,a_2_0_orders_2(sK0,X4))
      | sK4(X5,sK0,X4) = X5
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f97,f55])).

fof(f97,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X5,a_2_0_orders_2(sK0,X4))
      | sK4(X5,sK0,X4) = X5
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f79,f93])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | sK4(X0,X1,X2) = X0
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f361,plain,(
    ! [X10] :
      ( r2_orders_2(sK0,X10,sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X10,k2_struct_0(sK0))
      | k1_xboole_0 = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f355,f143])).

fof(f355,plain,(
    ! [X10] :
      ( r2_orders_2(sK0,X10,sK4(sK1(a_2_0_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X10,k2_struct_0(sK0))
      | k1_xboole_0 = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f251,f87])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK4(sK1(a_2_0_orders_2(sK0,X1)),sK0,X1))
      | ~ r2_hidden(X0,X1)
      | k1_xboole_0 = a_2_0_orders_2(sK0,X1) ) ),
    inference(resolution,[],[f164,f65])).

fof(f164,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ r2_hidden(X2,X3)
      | r2_orders_2(sK0,X2,sK4(X4,sK0,X3))
      | ~ r1_tarski(X3,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f126,f76])).

fof(f126,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X7,X6)
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X6))
      | r2_orders_2(sK0,X7,sK4(X8,sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f125,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f125,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X7,k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X6))
      | r2_orders_2(sK0,X7,sK4(X8,sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f124,f51])).

fof(f124,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X7,k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X6))
      | r2_orders_2(sK0,X7,sK4(X8,sK0,X6))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f52])).

fof(f123,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X7,k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X6))
      | r2_orders_2(sK0,X7,sK4(X8,sK0,X6))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f53])).

fof(f122,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X7,k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X6))
      | r2_orders_2(sK0,X7,sK4(X8,sK0,X6))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f54])).

fof(f121,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X7,k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X6))
      | r2_orders_2(sK0,X7,sK4(X8,sK0,X6))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f55])).

fof(f98,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X7,k2_struct_0(sK0))
      | ~ r2_hidden(X8,a_2_0_orders_2(sK0,X6))
      | r2_orders_2(sK0,X7,sK4(X8,sK0,X6))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f80,f93])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f801,plain,
    ( ! [X1] :
        ( r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),X1)
        | ~ r1_tarski(k1_orders_2(sK0,k1_xboole_0),X1) )
    | ~ spl5_12
    | spl5_15 ),
    inference(resolution,[],[f751,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f751,plain,
    ( r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k1_xboole_0))
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f748,f426])).

fof(f426,plain,
    ( ~ r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl5_15
  <=> r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f748,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0)
    | r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k1_xboole_0))
    | ~ spl5_12 ),
    inference(resolution,[],[f730,f380])).

fof(f730,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_hidden(sK3(sK0,k1_xboole_0,X0),k1_xboole_0)
      | r2_hidden(X0,k1_orders_2(sK0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f700,f710])).

fof(f710,plain,(
    k1_orders_2(sK0,k1_xboole_0) = a_2_0_orders_2(sK0,k1_xboole_0) ),
    inference(resolution,[],[f138,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f700,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_hidden(X0,a_2_0_orders_2(sK0,k1_xboole_0)) ) ),
    inference(resolution,[],[f131,f58])).

fof(f131,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X9,X10),X9)
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X10,a_2_0_orders_2(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f130,f51])).

fof(f130,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X9,X10),X9)
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X10,a_2_0_orders_2(sK0,X9))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f52])).

fof(f129,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X9,X10),X9)
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X10,a_2_0_orders_2(sK0,X9))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f53])).

fof(f128,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X9,X10),X9)
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X10,a_2_0_orders_2(sK0,X9))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f54])).

fof(f127,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X9,X10),X9)
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X10,a_2_0_orders_2(sK0,X9))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f55])).

fof(f99,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X9,X10),X9)
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X10,a_2_0_orders_2(sK0,X9))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f89,f93])).

fof(f89,plain,(
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
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f728,plain,(
    ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f725,f57])).

fof(f725,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))))
    | ~ spl5_15 ),
    inference(resolution,[],[f427,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f427,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f425])).

fof(f417,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f415,f56])).

fof(f415,plain,
    ( k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))
    | spl5_12 ),
    inference(subsumption_resolution,[],[f413,f87])).

fof(f413,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))
    | spl5_12 ),
    inference(resolution,[],[f381,f216])).

fof(f216,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(k1_orders_2(sK0,X0)),k2_struct_0(sK0))
      | ~ r1_tarski(X0,k2_struct_0(sK0))
      | k1_xboole_0 = k1_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f212,f65])).

fof(f212,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,X2))
      | m1_subset_1(X1,k2_struct_0(sK0))
      | ~ r1_tarski(X2,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f140,f76])).

fof(f140,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(X2,k2_struct_0(sK0))
      | ~ r2_hidden(X2,k1_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f110,f84])).

fof(f381,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:43:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (17107)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.47  % (17091)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (17082)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (17108)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (17079)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.58  % (17090)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (17100)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (17098)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.59  % (17086)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.59  % (17104)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.60  % (17080)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.70/0.60  % (17081)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.70/0.60  % (17092)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.98/0.62  % (17095)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.98/0.62  % (17078)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.98/0.62  % (17103)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.98/0.62  % (17083)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.98/0.63  % (17096)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.98/0.63  % (17087)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.98/0.63  % (17097)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.98/0.63  % (17085)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.98/0.63  % (17101)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.98/0.63  % (17106)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.98/0.64  % (17101)Refutation not found, incomplete strategy% (17101)------------------------------
% 1.98/0.64  % (17101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (17101)Termination reason: Refutation not found, incomplete strategy
% 1.98/0.64  
% 1.98/0.64  % (17101)Memory used [KB]: 10746
% 1.98/0.64  % (17101)Time elapsed: 0.206 s
% 1.98/0.64  % (17101)------------------------------
% 1.98/0.64  % (17101)------------------------------
% 1.98/0.64  % (17089)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.98/0.64  % (17094)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.98/0.64  % (17109)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.98/0.64  % (17099)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.98/0.65  % (17102)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.98/0.65  % (17093)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.98/0.66  % (17084)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.38/0.71  % (17086)Refutation found. Thanks to Tanya!
% 2.38/0.71  % SZS status Theorem for theBenchmark
% 2.38/0.71  % SZS output start Proof for theBenchmark
% 2.38/0.71  fof(f1106,plain,(
% 2.38/0.71    $false),
% 2.38/0.71    inference(avatar_sat_refutation,[],[f417,f728,f1102])).
% 2.38/0.71  fof(f1102,plain,(
% 2.38/0.71    ~spl5_12 | spl5_15),
% 2.38/0.71    inference(avatar_contradiction_clause,[],[f1101])).
% 2.38/0.71  fof(f1101,plain,(
% 2.38/0.71    $false | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(subsumption_resolution,[],[f1100,f380])).
% 2.38/0.71  fof(f380,plain,(
% 2.38/0.71    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl5_12),
% 2.38/0.71    inference(avatar_component_clause,[],[f379])).
% 2.38/0.71  fof(f379,plain,(
% 2.38/0.71    spl5_12 <=> m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 2.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.38/0.71  fof(f1100,plain,(
% 2.38/0.71    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(forward_demodulation,[],[f1099,f93])).
% 2.38/0.71  fof(f93,plain,(
% 2.38/0.71    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 2.38/0.71    inference(resolution,[],[f92,f59])).
% 2.38/0.71  fof(f59,plain,(
% 2.38/0.71    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f19])).
% 2.38/0.71  fof(f19,plain,(
% 2.38/0.71    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.38/0.71    inference(ennf_transformation,[],[f9])).
% 2.38/0.71  fof(f9,axiom,(
% 2.38/0.71    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.38/0.71  fof(f92,plain,(
% 2.38/0.71    l1_struct_0(sK0)),
% 2.38/0.71    inference(resolution,[],[f55,f60])).
% 2.38/0.71  fof(f60,plain,(
% 2.38/0.71    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f20])).
% 2.38/0.71  fof(f20,plain,(
% 2.38/0.71    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.38/0.71    inference(ennf_transformation,[],[f13])).
% 2.38/0.71  fof(f13,axiom,(
% 2.38/0.71    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 2.38/0.71  fof(f55,plain,(
% 2.38/0.71    l1_orders_2(sK0)),
% 2.38/0.71    inference(cnf_transformation,[],[f34])).
% 2.38/0.71  fof(f34,plain,(
% 2.38/0.71    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.38/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f33])).
% 2.38/0.71  fof(f33,plain,(
% 2.38/0.71    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.38/0.71    introduced(choice_axiom,[])).
% 2.38/0.71  fof(f18,plain,(
% 2.38/0.71    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.38/0.71    inference(flattening,[],[f17])).
% 2.38/0.71  fof(f17,plain,(
% 2.38/0.71    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.38/0.71    inference(ennf_transformation,[],[f16])).
% 2.38/0.71  fof(f16,negated_conjecture,(
% 2.38/0.71    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.38/0.71    inference(negated_conjecture,[],[f15])).
% 2.38/0.71  fof(f15,conjecture,(
% 2.38/0.71    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).
% 2.38/0.71  fof(f1099,plain,(
% 2.38/0.71    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(subsumption_resolution,[],[f1096,f55])).
% 2.38/0.71  fof(f1096,plain,(
% 2.38/0.71    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(resolution,[],[f1084,f91])).
% 2.38/0.71  fof(f91,plain,(
% 2.38/0.71    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.38/0.71    inference(duplicate_literal_removal,[],[f85])).
% 2.38/0.71  fof(f85,plain,(
% 2.38/0.71    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.38/0.71    inference(equality_resolution,[],[f62])).
% 2.38/0.71  fof(f62,plain,(
% 2.38/0.71    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f36])).
% 2.38/0.71  fof(f36,plain,(
% 2.38/0.71    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.38/0.71    inference(flattening,[],[f35])).
% 2.38/0.71  fof(f35,plain,(
% 2.38/0.71    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.38/0.71    inference(nnf_transformation,[],[f21])).
% 2.38/0.71  fof(f21,plain,(
% 2.38/0.71    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.38/0.71    inference(ennf_transformation,[],[f10])).
% 2.38/0.71  fof(f10,axiom,(
% 2.38/0.71    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 2.38/0.71  fof(f1084,plain,(
% 2.38/0.71    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(subsumption_resolution,[],[f1073,f720])).
% 2.38/0.71  fof(f720,plain,(
% 2.38/0.71    r1_tarski(k1_orders_2(sK0,k1_xboole_0),k2_struct_0(sK0))),
% 2.38/0.71    inference(resolution,[],[f141,f58])).
% 2.38/0.71  fof(f58,plain,(
% 2.38/0.71    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.38/0.71    inference(cnf_transformation,[],[f4])).
% 2.38/0.71  fof(f4,axiom,(
% 2.38/0.71    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.38/0.71  fof(f141,plain,(
% 2.38/0.71    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_orders_2(sK0,X3),k2_struct_0(sK0))) )),
% 2.38/0.71    inference(resolution,[],[f110,f75])).
% 2.38/0.71  fof(f75,plain,(
% 2.38/0.71    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f45])).
% 2.38/0.71  fof(f45,plain,(
% 2.38/0.71    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.38/0.71    inference(nnf_transformation,[],[f5])).
% 2.38/0.71  fof(f5,axiom,(
% 2.38/0.71    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.38/0.71  fof(f110,plain,(
% 2.38/0.71    ( ! [X1] : (m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f109,f51])).
% 2.38/0.71  fof(f51,plain,(
% 2.38/0.71    ~v2_struct_0(sK0)),
% 2.38/0.71    inference(cnf_transformation,[],[f34])).
% 2.38/0.71  fof(f109,plain,(
% 2.38/0.71    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f108,f52])).
% 2.38/0.71  fof(f52,plain,(
% 2.38/0.71    v3_orders_2(sK0)),
% 2.38/0.71    inference(cnf_transformation,[],[f34])).
% 2.38/0.71  fof(f108,plain,(
% 2.38/0.71    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f107,f53])).
% 2.38/0.71  fof(f53,plain,(
% 2.38/0.71    v4_orders_2(sK0)),
% 2.38/0.71    inference(cnf_transformation,[],[f34])).
% 2.38/0.71  fof(f107,plain,(
% 2.38/0.71    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f106,f54])).
% 2.38/0.71  fof(f54,plain,(
% 2.38/0.71    v5_orders_2(sK0)),
% 2.38/0.71    inference(cnf_transformation,[],[f34])).
% 2.38/0.71  fof(f106,plain,(
% 2.38/0.71    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f95,f55])).
% 2.38/0.71  fof(f95,plain,(
% 2.38/0.71    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(superposition,[],[f68,f93])).
% 2.38/0.71  fof(f68,plain,(
% 2.38/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f26])).
% 2.38/0.71  fof(f26,plain,(
% 2.38/0.71    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.38/0.71    inference(flattening,[],[f25])).
% 2.38/0.71  fof(f25,plain,(
% 2.38/0.71    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.38/0.71    inference(ennf_transformation,[],[f12])).
% 2.38/0.71  fof(f12,axiom,(
% 2.38/0.71    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 2.38/0.71  fof(f1073,plain,(
% 2.38/0.71    ~r1_tarski(k1_orders_2(sK0,k1_xboole_0),k2_struct_0(sK0)) | r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(resolution,[],[f801,f364])).
% 2.38/0.71  fof(f364,plain,(
% 2.38/0.71    ( ! [X10] : (~r2_hidden(X10,k2_struct_0(sK0)) | r2_orders_2(sK0,X10,sK1(k1_orders_2(sK0,k2_struct_0(sK0))))) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f363,f56])).
% 2.38/0.71  fof(f56,plain,(
% 2.38/0.71    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))),
% 2.38/0.71    inference(cnf_transformation,[],[f34])).
% 2.38/0.71  fof(f363,plain,(
% 2.38/0.71    ( ! [X10] : (k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) | r2_orders_2(sK0,X10,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X10,k2_struct_0(sK0))) )),
% 2.38/0.71    inference(forward_demodulation,[],[f362,f143])).
% 2.38/0.71  fof(f143,plain,(
% 2.38/0.71    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0))),
% 2.38/0.71    inference(resolution,[],[f138,f87])).
% 2.38/0.71  fof(f87,plain,(
% 2.38/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.38/0.71    inference(equality_resolution,[],[f69])).
% 2.38/0.71  fof(f69,plain,(
% 2.38/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.38/0.71    inference(cnf_transformation,[],[f40])).
% 2.38/0.71  fof(f40,plain,(
% 2.38/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.38/0.71    inference(flattening,[],[f39])).
% 2.38/0.71  fof(f39,plain,(
% 2.38/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.38/0.71    inference(nnf_transformation,[],[f2])).
% 2.38/0.71  fof(f2,axiom,(
% 2.38/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.38/0.71  fof(f138,plain,(
% 2.38/0.71    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 2.38/0.71    inference(resolution,[],[f105,f76])).
% 2.38/0.71  fof(f76,plain,(
% 2.38/0.71    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f45])).
% 2.38/0.71  fof(f105,plain,(
% 2.38/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f104,f51])).
% 2.38/0.71  fof(f104,plain,(
% 2.38/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f103,f52])).
% 2.38/0.71  fof(f103,plain,(
% 2.38/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f102,f53])).
% 2.38/0.71  fof(f102,plain,(
% 2.38/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f101,f54])).
% 2.38/0.71  fof(f101,plain,(
% 2.38/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f94,f55])).
% 2.38/0.71  fof(f94,plain,(
% 2.38/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(superposition,[],[f64,f93])).
% 2.38/0.71  fof(f64,plain,(
% 2.38/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f23])).
% 2.38/0.71  fof(f23,plain,(
% 2.38/0.71    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.38/0.71    inference(flattening,[],[f22])).
% 2.38/0.71  fof(f22,plain,(
% 2.38/0.71    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.38/0.71    inference(ennf_transformation,[],[f11])).
% 2.38/0.71  fof(f11,axiom,(
% 2.38/0.71    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 2.38/0.71  fof(f362,plain,(
% 2.38/0.71    ( ! [X10] : (r2_orders_2(sK0,X10,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X10,k2_struct_0(sK0)) | k1_xboole_0 = a_2_0_orders_2(sK0,k2_struct_0(sK0))) )),
% 2.38/0.71    inference(forward_demodulation,[],[f361,f226])).
% 2.38/0.71  fof(f226,plain,(
% 2.38/0.71    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 2.38/0.71    inference(subsumption_resolution,[],[f224,f56])).
% 2.38/0.71  fof(f224,plain,(
% 2.38/0.71    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0))),
% 2.38/0.71    inference(resolution,[],[f223,f65])).
% 2.38/0.71  fof(f65,plain,(
% 2.38/0.71    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.38/0.71    inference(cnf_transformation,[],[f38])).
% 2.38/0.71  fof(f38,plain,(
% 2.38/0.71    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.38/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f37])).
% 2.38/0.71  fof(f37,plain,(
% 2.38/0.71    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.38/0.71    introduced(choice_axiom,[])).
% 2.38/0.71  fof(f24,plain,(
% 2.38/0.71    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.38/0.71    inference(ennf_transformation,[],[f8])).
% 2.38/0.71  fof(f8,axiom,(
% 2.38/0.71    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.38/0.71  fof(f223,plain,(
% 2.38/0.71    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f221,f87])).
% 2.38/0.71  fof(f221,plain,(
% 2.38/0.71    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X0,sK0,k2_struct_0(sK0)) = X0 | ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))) )),
% 2.38/0.71    inference(superposition,[],[f146,f143])).
% 2.38/0.71  fof(f146,plain,(
% 2.38/0.71    ( ! [X2,X1] : (~r2_hidden(X1,a_2_0_orders_2(sK0,X2)) | sK4(X1,sK0,X2) = X1 | ~r1_tarski(X2,k2_struct_0(sK0))) )),
% 2.38/0.71    inference(resolution,[],[f120,f76])).
% 2.38/0.71  fof(f120,plain,(
% 2.38/0.71    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X5,a_2_0_orders_2(sK0,X4)) | sK4(X5,sK0,X4) = X5) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f119,f51])).
% 2.38/0.71  fof(f119,plain,(
% 2.38/0.71    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X5,a_2_0_orders_2(sK0,X4)) | sK4(X5,sK0,X4) = X5 | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f118,f52])).
% 2.38/0.71  fof(f118,plain,(
% 2.38/0.71    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X5,a_2_0_orders_2(sK0,X4)) | sK4(X5,sK0,X4) = X5 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f117,f53])).
% 2.38/0.71  fof(f117,plain,(
% 2.38/0.71    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X5,a_2_0_orders_2(sK0,X4)) | sK4(X5,sK0,X4) = X5 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f116,f54])).
% 2.38/0.71  fof(f116,plain,(
% 2.38/0.71    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X5,a_2_0_orders_2(sK0,X4)) | sK4(X5,sK0,X4) = X5 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f97,f55])).
% 2.38/0.71  fof(f97,plain,(
% 2.38/0.71    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X5,a_2_0_orders_2(sK0,X4)) | sK4(X5,sK0,X4) = X5 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(superposition,[],[f79,f93])).
% 2.38/0.71  fof(f79,plain,(
% 2.38/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | sK4(X0,X1,X2) = X0 | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f50])).
% 2.38/0.71  fof(f50,plain,(
% 2.38/0.71    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.38/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).
% 2.38/0.71  fof(f48,plain,(
% 2.38/0.71    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 2.38/0.71    introduced(choice_axiom,[])).
% 2.38/0.71  fof(f49,plain,(
% 2.38/0.71    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 2.38/0.71    introduced(choice_axiom,[])).
% 2.38/0.71  fof(f47,plain,(
% 2.38/0.71    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.38/0.71    inference(rectify,[],[f46])).
% 2.38/0.71  fof(f46,plain,(
% 2.38/0.71    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.38/0.71    inference(nnf_transformation,[],[f30])).
% 2.38/0.71  fof(f30,plain,(
% 2.38/0.71    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.38/0.71    inference(flattening,[],[f29])).
% 2.38/0.71  fof(f29,plain,(
% 2.38/0.71    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.38/0.71    inference(ennf_transformation,[],[f14])).
% 2.38/0.71  fof(f14,axiom,(
% 2.38/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 2.38/0.71  fof(f361,plain,(
% 2.38/0.71    ( ! [X10] : (r2_orders_2(sK0,X10,sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) | ~r2_hidden(X10,k2_struct_0(sK0)) | k1_xboole_0 = a_2_0_orders_2(sK0,k2_struct_0(sK0))) )),
% 2.38/0.71    inference(forward_demodulation,[],[f355,f143])).
% 2.38/0.71  fof(f355,plain,(
% 2.38/0.71    ( ! [X10] : (r2_orders_2(sK0,X10,sK4(sK1(a_2_0_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) | ~r2_hidden(X10,k2_struct_0(sK0)) | k1_xboole_0 = a_2_0_orders_2(sK0,k2_struct_0(sK0))) )),
% 2.38/0.71    inference(resolution,[],[f251,f87])).
% 2.38/0.71  fof(f251,plain,(
% 2.38/0.71    ( ! [X0,X1] : (~r1_tarski(X1,k2_struct_0(sK0)) | r2_orders_2(sK0,X0,sK4(sK1(a_2_0_orders_2(sK0,X1)),sK0,X1)) | ~r2_hidden(X0,X1) | k1_xboole_0 = a_2_0_orders_2(sK0,X1)) )),
% 2.38/0.71    inference(resolution,[],[f164,f65])).
% 2.38/0.71  fof(f164,plain,(
% 2.38/0.71    ( ! [X4,X2,X3] : (~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~r2_hidden(X2,X3) | r2_orders_2(sK0,X2,sK4(X4,sK0,X3)) | ~r1_tarski(X3,k2_struct_0(sK0))) )),
% 2.38/0.71    inference(resolution,[],[f126,f76])).
% 2.38/0.71  fof(f126,plain,(
% 2.38/0.71    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X7,X6) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X6)) | r2_orders_2(sK0,X7,sK4(X8,sK0,X6))) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f125,f84])).
% 2.38/0.71  fof(f84,plain,(
% 2.38/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f32])).
% 2.38/0.71  fof(f32,plain,(
% 2.38/0.71    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.38/0.71    inference(flattening,[],[f31])).
% 2.38/0.71  fof(f31,plain,(
% 2.38/0.71    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.38/0.71    inference(ennf_transformation,[],[f6])).
% 2.38/0.71  fof(f6,axiom,(
% 2.38/0.71    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.38/0.71  fof(f125,plain,(
% 2.38/0.71    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X7,X6) | ~m1_subset_1(X7,k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X6)) | r2_orders_2(sK0,X7,sK4(X8,sK0,X6))) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f124,f51])).
% 2.38/0.71  fof(f124,plain,(
% 2.38/0.71    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X7,X6) | ~m1_subset_1(X7,k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X6)) | r2_orders_2(sK0,X7,sK4(X8,sK0,X6)) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f123,f52])).
% 2.38/0.71  fof(f123,plain,(
% 2.38/0.71    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X7,X6) | ~m1_subset_1(X7,k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X6)) | r2_orders_2(sK0,X7,sK4(X8,sK0,X6)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f122,f53])).
% 2.38/0.71  fof(f122,plain,(
% 2.38/0.71    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X7,X6) | ~m1_subset_1(X7,k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X6)) | r2_orders_2(sK0,X7,sK4(X8,sK0,X6)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f121,f54])).
% 2.38/0.71  fof(f121,plain,(
% 2.38/0.71    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X7,X6) | ~m1_subset_1(X7,k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X6)) | r2_orders_2(sK0,X7,sK4(X8,sK0,X6)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f98,f55])).
% 2.38/0.71  fof(f98,plain,(
% 2.38/0.71    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X7,X6) | ~m1_subset_1(X7,k2_struct_0(sK0)) | ~r2_hidden(X8,a_2_0_orders_2(sK0,X6)) | r2_orders_2(sK0,X7,sK4(X8,sK0,X6)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(superposition,[],[f80,f93])).
% 2.38/0.71  fof(f80,plain,(
% 2.38/0.71    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f50])).
% 2.38/0.71  fof(f801,plain,(
% 2.38/0.71    ( ! [X1] : (r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),X1) | ~r1_tarski(k1_orders_2(sK0,k1_xboole_0),X1)) ) | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(resolution,[],[f751,f72])).
% 2.38/0.71  fof(f72,plain,(
% 2.38/0.71    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f44])).
% 2.38/0.71  fof(f44,plain,(
% 2.38/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 2.38/0.71  fof(f43,plain,(
% 2.38/0.71    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.38/0.71    introduced(choice_axiom,[])).
% 2.38/0.71  fof(f42,plain,(
% 2.38/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.71    inference(rectify,[],[f41])).
% 2.38/0.71  fof(f41,plain,(
% 2.38/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.71    inference(nnf_transformation,[],[f27])).
% 2.38/0.71  fof(f27,plain,(
% 2.38/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.38/0.71    inference(ennf_transformation,[],[f1])).
% 2.38/0.71  fof(f1,axiom,(
% 2.38/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.38/0.71  fof(f751,plain,(
% 2.38/0.71    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k1_xboole_0)) | (~spl5_12 | spl5_15)),
% 2.38/0.71    inference(subsumption_resolution,[],[f748,f426])).
% 2.38/0.71  fof(f426,plain,(
% 2.38/0.71    ~r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0) | spl5_15),
% 2.38/0.71    inference(avatar_component_clause,[],[f425])).
% 2.38/0.71  fof(f425,plain,(
% 2.38/0.71    spl5_15 <=> r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0)),
% 2.38/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.38/0.71  fof(f748,plain,(
% 2.38/0.71    r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0) | r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k1_xboole_0)) | ~spl5_12),
% 2.38/0.71    inference(resolution,[],[f730,f380])).
% 2.38/0.71  fof(f730,plain,(
% 2.38/0.71    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(sK3(sK0,k1_xboole_0,X0),k1_xboole_0) | r2_hidden(X0,k1_orders_2(sK0,k1_xboole_0))) )),
% 2.38/0.71    inference(forward_demodulation,[],[f700,f710])).
% 2.38/0.71  fof(f710,plain,(
% 2.38/0.71    k1_orders_2(sK0,k1_xboole_0) = a_2_0_orders_2(sK0,k1_xboole_0)),
% 2.38/0.71    inference(resolution,[],[f138,f57])).
% 2.38/0.71  fof(f57,plain,(
% 2.38/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f3])).
% 2.38/0.71  fof(f3,axiom,(
% 2.38/0.71    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.38/0.71  fof(f700,plain,(
% 2.38/0.71    ( ! [X0] : (r2_hidden(sK3(sK0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,a_2_0_orders_2(sK0,k1_xboole_0))) )),
% 2.38/0.71    inference(resolution,[],[f131,f58])).
% 2.38/0.71  fof(f131,plain,(
% 2.38/0.71    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X9,X10),X9) | ~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X10,a_2_0_orders_2(sK0,X9))) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f130,f51])).
% 2.38/0.71  fof(f130,plain,(
% 2.38/0.71    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X9,X10),X9) | ~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X10,a_2_0_orders_2(sK0,X9)) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f129,f52])).
% 2.38/0.71  fof(f129,plain,(
% 2.38/0.71    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X9,X10),X9) | ~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X10,a_2_0_orders_2(sK0,X9)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f128,f53])).
% 2.38/0.71  fof(f128,plain,(
% 2.38/0.71    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X9,X10),X9) | ~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X10,a_2_0_orders_2(sK0,X9)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f127,f54])).
% 2.38/0.71  fof(f127,plain,(
% 2.38/0.71    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X9,X10),X9) | ~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X10,a_2_0_orders_2(sK0,X9)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(subsumption_resolution,[],[f99,f55])).
% 2.38/0.71  fof(f99,plain,(
% 2.38/0.71    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X9,X10),X9) | ~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X10,a_2_0_orders_2(sK0,X9)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.38/0.71    inference(superposition,[],[f89,f93])).
% 2.38/0.71  fof(f89,plain,(
% 2.38/0.71    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.38/0.71    inference(equality_resolution,[],[f82])).
% 2.38/0.71  fof(f82,plain,(
% 2.38/0.71    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f50])).
% 2.38/0.71  fof(f728,plain,(
% 2.38/0.71    ~spl5_15),
% 2.38/0.71    inference(avatar_contradiction_clause,[],[f727])).
% 2.38/0.71  fof(f727,plain,(
% 2.38/0.71    $false | ~spl5_15),
% 2.38/0.71    inference(subsumption_resolution,[],[f725,f57])).
% 2.38/0.71  fof(f725,plain,(
% 2.38/0.71    ~r1_tarski(k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))))) | ~spl5_15),
% 2.38/0.71    inference(resolution,[],[f427,f77])).
% 2.38/0.71  fof(f77,plain,(
% 2.38/0.71    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.38/0.71    inference(cnf_transformation,[],[f28])).
% 2.38/0.71  fof(f28,plain,(
% 2.38/0.71    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.38/0.71    inference(ennf_transformation,[],[f7])).
% 2.38/0.71  fof(f7,axiom,(
% 2.38/0.71    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.38/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.38/0.71  fof(f427,plain,(
% 2.38/0.71    r2_hidden(sK3(sK0,k1_xboole_0,sK1(k1_orders_2(sK0,k2_struct_0(sK0)))),k1_xboole_0) | ~spl5_15),
% 2.38/0.71    inference(avatar_component_clause,[],[f425])).
% 2.38/0.71  fof(f417,plain,(
% 2.38/0.71    spl5_12),
% 2.38/0.71    inference(avatar_contradiction_clause,[],[f416])).
% 2.38/0.71  fof(f416,plain,(
% 2.38/0.71    $false | spl5_12),
% 2.38/0.71    inference(subsumption_resolution,[],[f415,f56])).
% 2.38/0.71  fof(f415,plain,(
% 2.38/0.71    k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) | spl5_12),
% 2.38/0.71    inference(subsumption_resolution,[],[f413,f87])).
% 2.38/0.71  fof(f413,plain,(
% 2.38/0.71    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,k2_struct_0(sK0)) | spl5_12),
% 2.38/0.71    inference(resolution,[],[f381,f216])).
% 2.38/0.71  fof(f216,plain,(
% 2.38/0.71    ( ! [X0] : (m1_subset_1(sK1(k1_orders_2(sK0,X0)),k2_struct_0(sK0)) | ~r1_tarski(X0,k2_struct_0(sK0)) | k1_xboole_0 = k1_orders_2(sK0,X0)) )),
% 2.38/0.71    inference(resolution,[],[f212,f65])).
% 2.38/0.71  fof(f212,plain,(
% 2.38/0.71    ( ! [X2,X1] : (~r2_hidden(X1,k1_orders_2(sK0,X2)) | m1_subset_1(X1,k2_struct_0(sK0)) | ~r1_tarski(X2,k2_struct_0(sK0))) )),
% 2.38/0.71    inference(resolution,[],[f140,f76])).
% 2.38/0.71  fof(f140,plain,(
% 2.38/0.71    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(X2,k2_struct_0(sK0)) | ~r2_hidden(X2,k1_orders_2(sK0,X1))) )),
% 2.38/0.71    inference(resolution,[],[f110,f84])).
% 2.38/0.71  fof(f381,plain,(
% 2.38/0.71    ~m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | spl5_12),
% 2.38/0.71    inference(avatar_component_clause,[],[f379])).
% 2.38/0.71  % SZS output end Proof for theBenchmark
% 2.38/0.71  % (17086)------------------------------
% 2.38/0.71  % (17086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.71  % (17086)Termination reason: Refutation
% 2.38/0.71  
% 2.38/0.71  % (17086)Memory used [KB]: 11385
% 2.38/0.71  % (17086)Time elapsed: 0.293 s
% 2.38/0.71  % (17086)------------------------------
% 2.38/0.71  % (17086)------------------------------
% 2.38/0.71  % (17077)Success in time 0.349 s
%------------------------------------------------------------------------------
