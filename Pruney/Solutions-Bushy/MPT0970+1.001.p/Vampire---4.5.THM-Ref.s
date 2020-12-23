%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0970+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:59 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 735 expanded)
%              Number of leaves         :   29 ( 234 expanded)
%              Depth                    :   25
%              Number of atoms          :  602 (3810 expanded)
%              Number of equality atoms :  141 (1104 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1587,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f176,f1058,f1083,f1084,f1099,f1254,f1537,f1544])).

fof(f1544,plain,
    ( ~ spl8_8
    | ~ spl8_25
    | ~ spl8_28
    | spl8_29 ),
    inference(avatar_contradiction_clause,[],[f1543])).

fof(f1543,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_25
    | ~ spl8_28
    | spl8_29 ),
    inference(subsumption_resolution,[],[f1542,f1531])).

fof(f1531,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | ~ spl8_8
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f1530,f1266])).

fof(f1266,plain,
    ( v1_funct_1(sK1)
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f49,f1082])).

fof(f1082,plain,
    ( sK1 = sK2
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1081,plain,
    ( spl8_28
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f1530,plain,
    ( ~ v1_funct_1(sK1)
    | v1_xboole_0(k1_relat_1(sK1))
    | ~ spl8_8
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f1525,f1281])).

fof(f1281,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_8
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f1235,f1082])).

fof(f1235,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f128,f441])).

fof(f441,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | v1_relat_1(X7) ) ),
    inference(superposition,[],[f111,f252])).

fof(f252,plain,(
    ! [X4,X5] :
      ( sK7(k1_zfmisc_1(k2_zfmisc_1(X5,X4))) = X4
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f154,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f7,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f64,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f56,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f111,plain,(
    ! [X0,X1] : v1_relat_1(sK7(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ),
    inference(resolution,[],[f68,f63])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f128,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1525,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(k1_relat_1(sK1))
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(resolution,[],[f1506,f237])).

fof(f237,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(k2_relat_1(X4))
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(k1_relat_1(X4)) ) ),
    inference(resolution,[],[f143,f100])).

fof(f100,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f63])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f143,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(k2_relat_1(X3)) ) ),
    inference(resolution,[],[f81,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f81,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f44,f43,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1506,plain,
    ( v1_xboole_0(k2_relat_1(sK1))
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(resolution,[],[f1299,f100])).

fof(f1299,plain,
    ( ! [X9] : ~ r2_hidden(X9,k2_relat_1(sK1))
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f1070,f1082])).

fof(f1070,plain,
    ( ! [X9] : ~ r2_hidden(X9,k2_relat_1(sK2))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f1069,plain,
    ( spl8_25
  <=> ! [X9] : ~ r2_hidden(X9,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f1542,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl8_28
    | spl8_29 ),
    inference(forward_demodulation,[],[f1087,f1082])).

fof(f1087,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1086,plain,
    ( spl8_29
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f1537,plain,
    ( ~ spl8_8
    | ~ spl8_28
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f1536])).

fof(f1536,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_28
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1535,f1268])).

fof(f1268,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_8
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f128,f1082])).

fof(f1535,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_32 ),
    inference(equality_resolution,[],[f1098])).

fof(f1098,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1097,plain,
    ( spl8_32
  <=> ! [X0] :
        ( sK1 != X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f1254,plain,
    ( spl8_7
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f1249])).

fof(f1249,plain,
    ( $false
    | spl8_7
    | ~ spl8_10 ),
    inference(resolution,[],[f1243,f55])).

fof(f55,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f1243,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl8_7
    | ~ spl8_10 ),
    inference(duplicate_literal_removal,[],[f1242])).

fof(f1242,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | spl8_7
    | ~ spl8_10 ),
    inference(superposition,[],[f1134,f56])).

fof(f1134,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_7
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f125,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl8_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f125,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1099,plain,
    ( ~ spl8_29
    | spl8_32 ),
    inference(avatar_split_clause,[],[f516,f1097,f1086])).

fof(f516,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_xboole_0(k1_relat_1(sK2))
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f515,f110])).

fof(f110,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f515,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_relat_1(sK2)
      | ~ v1_xboole_0(k1_relat_1(sK2))
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f492,f49])).

fof(f492,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_xboole_0(k1_relat_1(sK2))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f133,f292])).

fof(f292,plain,(
    ! [X2,X3] :
      ( k2_relat_1(X2) = X3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_xboole_0(k1_relat_1(X2))
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f165,f67])).

fof(f165,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3),X3)
      | k2_relat_1(X2) = X3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_xboole_0(k1_relat_1(X2)) ) ),
    inference(resolution,[],[f60,f67])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f133,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f132,f51])).

fof(f132,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f54,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f1084,plain,
    ( spl8_25
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f226,f124,f1069])).

fof(f226,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f223,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f223,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f140,f51])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f71,f70])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f1083,plain,
    ( ~ spl8_7
    | spl8_28 ),
    inference(avatar_split_clause,[],[f251,f1081,f124])).

fof(f251,plain,
    ( sK1 = sK2
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f154,f51])).

fof(f1058,plain,
    ( spl8_7
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f1057])).

fof(f1057,plain,
    ( $false
    | spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f1056,f133])).

fof(f1056,plain,
    ( sK1 = k2_relat_1(sK2)
    | spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f1053,f1023])).

fof(f1023,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f1021,f133])).

fof(f1021,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | spl8_7
    | ~ spl8_9 ),
    inference(factoring,[],[f329])).

fof(f329,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | k2_relat_1(sK2) = X2
        | r2_hidden(sK4(sK2,X2),X2) )
    | spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f328,f192])).

fof(f192,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),sK0)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f191,f110])).

fof(f191,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),sK0)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f189,f49])).

fof(f189,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),sK0)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_9 ),
    inference(superposition,[],[f60,f179])).

fof(f179,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f177,f51])).

fof(f177,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_9 ),
    inference(superposition,[],[f172,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f328,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | ~ r2_hidden(sK5(sK2,X2),sK0)
        | k2_relat_1(sK2) = X2
        | r2_hidden(sK4(sK2,X2),X2) )
    | spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f327,f110])).

fof(f327,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | ~ r2_hidden(sK5(sK2,X2),sK0)
        | k2_relat_1(sK2) = X2
        | r2_hidden(sK4(sK2,X2),X2)
        | ~ v1_relat_1(sK2) )
    | spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f323,f49])).

fof(f323,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | ~ r2_hidden(sK5(sK2,X2),sK0)
        | k2_relat_1(sK2) = X2
        | r2_hidden(sK4(sK2,X2),X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | spl8_7
    | ~ spl8_9 ),
    inference(superposition,[],[f310,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f310,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f306,f125])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | v1_xboole_0(sK1)
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl8_9 ),
    inference(resolution,[],[f270,f66])).

fof(f270,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_funct_1(sK2,X1),sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f269,f179])).

fof(f269,plain,(
    ! [X1] :
      ( m1_subset_1(k1_funct_1(sK2,X1),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f268,f110])).

fof(f268,plain,(
    ! [X1] :
      ( m1_subset_1(k1_funct_1(sK2,X1),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f266,f49])).

fof(f266,plain,(
    ! [X1] :
      ( m1_subset_1(k1_funct_1(sK2,X1),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f225,f81])).

fof(f225,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f223,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1053,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | spl8_7
    | ~ spl8_9 ),
    inference(resolution,[],[f1023,f212])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f203])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( sK4(sK2,X1) != X0
        | k2_relat_1(sK2) = X1
        | ~ r2_hidden(sK4(sK2,X1),X1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f202,f52])).

fof(f52,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0),sK0)
        | sK4(sK2,X1) != X0
        | k2_relat_1(sK2) = X1
        | ~ r2_hidden(sK4(sK2,X1),X1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f201,f179])).

fof(f201,plain,(
    ! [X0,X1] :
      ( sK4(sK2,X1) != X0
      | k2_relat_1(sK2) = X1
      | ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ r2_hidden(sK4(sK2,X1),X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f200,f110])).

fof(f200,plain,(
    ! [X0,X1] :
      ( sK4(sK2,X1) != X0
      | k2_relat_1(sK2) = X1
      | ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ r2_hidden(sK4(sK2,X1),X1)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f195,f49])).

fof(f195,plain,(
    ! [X0,X1] :
      ( sK4(sK2,X1) != X0
      | k2_relat_1(sK2) = X1
      | ~ r2_hidden(sK3(X0),k1_relat_1(sK2))
      | ~ r2_hidden(sK4(sK2,X1),X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f62,f53])).

fof(f53,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK4(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f176,plain,
    ( spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f169,f174,f171])).

fof(f169,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f167,f50])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f167,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f129,plain,
    ( ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f121,f127,f124])).

fof(f121,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f64,f51])).

%------------------------------------------------------------------------------
