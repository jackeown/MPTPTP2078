%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 632 expanded)
%              Number of leaves         :   22 ( 162 expanded)
%              Depth                    :   36
%              Number of atoms          :  605 (3006 expanded)
%              Number of equality atoms :   60 ( 456 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f375,f422,f426,f462,f495,f501])).

fof(f501,plain,
    ( ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f453,f397])).

fof(f397,plain,
    ( sP4(k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl5_14
  <=> sP4(k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f453,plain,
    ( ~ sP4(k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_17 ),
    inference(resolution,[],[f420,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP4(X1) ) ),
    inference(general_splitting,[],[f67,f72_D])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f72_D])).

fof(f72_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f420,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl5_17
  <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f495,plain,
    ( ~ spl5_2
    | ~ spl5_12
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f484,f106])).

fof(f106,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_2
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f484,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f380,f398])).

fof(f398,plain,
    ( ~ sP4(k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f396])).

fof(f380,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | sP4(k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(resolution,[],[f360,f72])).

fof(f360,plain,
    ( m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl5_12
  <=> m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f462,plain,
    ( spl5_2
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | spl5_2
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f460,f385])).

fof(f385,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f383,f49])).

fof(f49,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
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
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f383,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f379,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2] :
                  ( r2_hidden(X2,X1)
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_mcart_1)).

fof(f379,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | m1_subset_1(X1,k2_struct_0(sK0)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f360,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f460,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | spl5_2
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f459,f76])).

fof(f76,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f75,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f48,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f459,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | spl5_2
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f458,f48])).

fof(f458,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl5_2
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f455,f387])).

fof(f387,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f386,f107])).

fof(f107,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f386,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f385,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f455,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f417,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f417,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
        | ~ r2_hidden(X0,k2_struct_0(sK0)) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl5_16
  <=> ! [X0] :
        ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
        | ~ r2_hidden(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f426,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl5_17 ),
    inference(subsumption_resolution,[],[f423,f49])).

fof(f423,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | spl5_17 ),
    inference(resolution,[],[f421,f57])).

fof(f421,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f419])).

fof(f422,plain,
    ( spl5_16
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f414,f419,f416])).

fof(f414,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f413,f96])).

fof(f96,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f80,f75])).

fof(f80,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f51,f76])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f413,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f412,f76])).

fof(f412,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f411,f130])).

fof(f130,plain,(
    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f95,f96])).

fof(f95,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f45,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f46])).

fof(f46,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f48])).

fof(f79,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f56,f76])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f411,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f410,f66])).

fof(f410,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f409,f44])).

fof(f409,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f408,f45])).

fof(f408,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f407,f46])).

fof(f407,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f406,f47])).

fof(f406,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f405,f48])).

fof(f405,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f62,f333])).

fof(f333,plain,(
    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f331,f49])).

fof(f331,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f327,f57])).

fof(f327,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1 ) ),
    inference(subsumption_resolution,[],[f326,f96])).

fof(f326,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1 ) ),
    inference(forward_demodulation,[],[f325,f76])).

fof(f325,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f324,f44])).

fof(f324,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f323,f45])).

fof(f323,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f322,f46])).

fof(f322,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f321,f47])).

fof(f321,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f312,f48])).

fof(f312,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f61,f130])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sK3(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f62,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f375,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f373,f96])).

fof(f373,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_12 ),
    inference(resolution,[],[f361,f90])).

fof(f90,plain,(
    ! [X2] :
      ( m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f89,f44])).

fof(f89,plain,(
    ! [X2] :
      ( m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f45])).

fof(f88,plain,(
    ! [X2] :
      ( m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,(
    ! [X2] :
      ( m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f47])).

fof(f86,plain,(
    ! [X2] :
      ( m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f48])).

fof(f78,plain,(
    ! [X2] :
      ( m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f59,f76])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f361,plain,
    ( ~ m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (15127)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (15142)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (15134)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (15131)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (15122)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (15144)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (15129)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (15136)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (15123)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (15137)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (15128)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (15140)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (15139)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (15124)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (15145)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (15130)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (15135)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (15128)Refutation not found, incomplete strategy% (15128)------------------------------
% 0.20/0.51  % (15128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15128)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15128)Memory used [KB]: 10618
% 0.20/0.51  % (15128)Time elapsed: 0.068 s
% 0.20/0.51  % (15128)------------------------------
% 0.20/0.51  % (15128)------------------------------
% 0.20/0.51  % (15126)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (15125)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (15123)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f502,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f375,f422,f426,f462,f495,f501])).
% 0.20/0.52  fof(f501,plain,(
% 0.20/0.52    ~spl5_14 | ~spl5_17),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f500])).
% 0.20/0.52  fof(f500,plain,(
% 0.20/0.52    $false | (~spl5_14 | ~spl5_17)),
% 0.20/0.52    inference(subsumption_resolution,[],[f453,f397])).
% 0.20/0.52  fof(f397,plain,(
% 0.20/0.52    sP4(k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl5_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f396])).
% 0.20/0.52  fof(f396,plain,(
% 0.20/0.52    spl5_14 <=> sP4(k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.52  fof(f453,plain,(
% 0.20/0.52    ~sP4(k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl5_17),
% 0.20/0.52    inference(resolution,[],[f420,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP4(X1)) )),
% 0.20/0.52    inference(general_splitting,[],[f67,f72_D])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP4(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f72_D])).
% 0.20/0.52  fof(f72_D,plain,(
% 0.20/0.52    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP4(X1)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.52  fof(f420,plain,(
% 0.20/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl5_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f419])).
% 0.20/0.52  fof(f419,plain,(
% 0.20/0.52    spl5_17 <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.52  fof(f495,plain,(
% 0.20/0.52    ~spl5_2 | ~spl5_12 | spl5_14),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f494])).
% 0.20/0.52  fof(f494,plain,(
% 0.20/0.52    $false | (~spl5_2 | ~spl5_12 | spl5_14)),
% 0.20/0.52    inference(subsumption_resolution,[],[f484,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    v1_xboole_0(k2_struct_0(sK0)) | ~spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl5_2 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f484,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_struct_0(sK0)) | (~spl5_12 | spl5_14)),
% 0.20/0.52    inference(subsumption_resolution,[],[f380,f398])).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    ~sP4(k2_orders_2(sK0,k2_struct_0(sK0))) | spl5_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f396])).
% 0.20/0.52  fof(f380,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_struct_0(sK0)) | sP4(k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl5_12),
% 0.20/0.52    inference(resolution,[],[f360,f72])).
% 0.20/0.52  fof(f360,plain,(
% 0.20/0.52    m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f359])).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    spl5_12 <=> m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.52  fof(f462,plain,(
% 0.20/0.52    spl5_2 | ~spl5_12 | ~spl5_16),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f461])).
% 0.20/0.52  fof(f461,plain,(
% 0.20/0.52    $false | (spl5_2 | ~spl5_12 | ~spl5_16)),
% 0.20/0.52    inference(subsumption_resolution,[],[f460,f385])).
% 0.20/0.52  fof(f385,plain,(
% 0.20/0.52    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl5_12),
% 0.20/0.52    inference(subsumption_resolution,[],[f383,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.20/0.52  fof(f383,plain,(
% 0.20/0.52    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | ~spl5_12),
% 0.20/0.52    inference(resolution,[],[f379,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~(! [X2] : (r2_hidden(X2,X1) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_mcart_1)).
% 0.20/0.52  fof(f379,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(X1,k2_struct_0(sK0))) ) | ~spl5_12),
% 0.20/0.52    inference(resolution,[],[f360,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.52  fof(f460,plain,(
% 0.20/0.52    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (spl5_2 | ~spl5_12 | ~spl5_16)),
% 0.20/0.52    inference(forward_demodulation,[],[f459,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f75,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    l1_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f48,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    l1_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f459,plain,(
% 0.20/0.52    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | (spl5_2 | ~spl5_12 | ~spl5_16)),
% 0.20/0.52    inference(subsumption_resolution,[],[f458,f48])).
% 0.20/0.52  fof(f458,plain,(
% 0.20/0.52    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | (spl5_2 | ~spl5_12 | ~spl5_16)),
% 0.20/0.52    inference(subsumption_resolution,[],[f455,f387])).
% 0.20/0.52  fof(f387,plain,(
% 0.20/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (spl5_2 | ~spl5_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f386,f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_struct_0(sK0)) | spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f105])).
% 0.20/0.52  fof(f386,plain,(
% 0.20/0.52    v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl5_12),
% 0.20/0.52    inference(resolution,[],[f385,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f455,plain,(
% 0.20/0.52    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl5_16),
% 0.20/0.52    inference(resolution,[],[f417,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(flattening,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.20/0.52  fof(f417,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0))) ) | ~spl5_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f416])).
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    spl5_16 <=> ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.52  fof(f426,plain,(
% 0.20/0.52    spl5_17),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f425])).
% 0.20/0.52  fof(f425,plain,(
% 0.20/0.52    $false | spl5_17),
% 0.20/0.52    inference(subsumption_resolution,[],[f423,f49])).
% 0.20/0.52  fof(f423,plain,(
% 0.20/0.52    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | spl5_17),
% 0.20/0.52    inference(resolution,[],[f421,f57])).
% 0.20/0.52  fof(f421,plain,(
% 0.20/0.52    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | spl5_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f419])).
% 0.20/0.52  fof(f422,plain,(
% 0.20/0.52    spl5_16 | ~spl5_17),
% 0.20/0.52    inference(avatar_split_clause,[],[f414,f419,f416])).
% 0.20/0.52  fof(f414,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f413,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f80,f75])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.20/0.52    inference(superposition,[],[f51,f76])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.20/0.52  fof(f413,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f412,f76])).
% 0.20/0.52  fof(f412,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f411,f130])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f95,f96])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f94,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f93,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    v3_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f92,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    v4_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f91,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    v5_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f79,f48])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X3) = a_2_1_orders_2(sK0,X3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(superposition,[],[f56,f76])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.20/0.52  fof(f411,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f410,f66])).
% 0.20/0.52  fof(f410,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f409,f44])).
% 0.20/0.52  fof(f409,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f408,f45])).
% 0.20/0.52  fof(f408,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f407,f46])).
% 0.20/0.52  fof(f407,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f406,f47])).
% 0.20/0.52  fof(f406,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f405,f48])).
% 0.20/0.52  fof(f405,plain,(
% 0.20/0.52    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(superposition,[],[f62,f333])).
% 0.20/0.52  fof(f333,plain,(
% 0.20/0.52    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f331,f49])).
% 0.20/0.52  fof(f331,plain,(
% 0.20/0.52    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f327,f57])).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f326,f96])).
% 0.20/0.52  fof(f326,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1) )),
% 0.20/0.52    inference(forward_demodulation,[],[f325,f76])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f324,f44])).
% 0.20/0.52  fof(f324,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f323,f45])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f322,f46])).
% 0.20/0.52  fof(f322,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f321,f47])).
% 0.20/0.52  fof(f321,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f312,f48])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(superposition,[],[f61,f130])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | sK3(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.52    inference(rectify,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f375,plain,(
% 0.20/0.52    spl5_12),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f374])).
% 0.20/0.52  fof(f374,plain,(
% 0.20/0.52    $false | spl5_12),
% 0.20/0.52    inference(subsumption_resolution,[],[f373,f96])).
% 0.20/0.52  fof(f373,plain,(
% 0.20/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_12),
% 0.20/0.52    inference(resolution,[],[f361,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f89,f44])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f88,f45])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f87,f46])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f86,f47])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f78,f48])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X2] : (m1_subset_1(k2_orders_2(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(superposition,[],[f59,f76])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 0.20/0.52  fof(f361,plain,(
% 0.20/0.52    ~m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f359])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (15123)------------------------------
% 0.20/0.52  % (15123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15123)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (15123)Memory used [KB]: 10746
% 0.20/0.52  % (15123)Time elapsed: 0.120 s
% 0.20/0.52  % (15123)------------------------------
% 0.20/0.52  % (15123)------------------------------
% 0.20/0.52  % (15121)Success in time 0.17 s
%------------------------------------------------------------------------------
