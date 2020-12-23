%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:15 EST 2020

% Result     : Theorem 5.46s
% Output     : Refutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 201 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   24
%              Number of atoms          :  433 ( 952 expanded)
%              Number of equality atoms :   86 ( 270 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1700,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f1697])).

fof(f1697,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1696])).

fof(f1696,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f1695,f77])).

fof(f77,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1695,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f1694,f82])).

fof(f82,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1694,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f1688,f87])).

fof(f87,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1688,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_4 ),
    inference(trivial_inequality_removal,[],[f1679])).

fof(f1679,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_4 ),
    inference(superposition,[],[f92,f1542])).

fof(f1542,plain,(
    ! [X21,X22,X20] :
      ( k1_funct_1(k7_relat_1(X22,X20),X21) = k1_funct_1(X22,X21)
      | ~ r2_hidden(X21,X20)
      | ~ v1_funct_1(X22)
      | ~ v1_relat_1(X22) ) ),
    inference(duplicate_literal_removal,[],[f1499])).

fof(f1499,plain,(
    ! [X21,X22,X20] :
      ( k1_funct_1(k7_relat_1(X22,X20),X21) = k1_funct_1(X22,X21)
      | ~ r2_hidden(X21,X20)
      | ~ v1_funct_1(X22)
      | ~ v1_relat_1(X22)
      | ~ r2_hidden(X21,X20) ) ),
    inference(superposition,[],[f963,f328])).

fof(f328,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f320])).

fof(f320,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f231,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK3(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X1,k2_relat_1(sK3(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f97,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK3(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK3(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK3(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK3(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK3(X0,X1)))
      | ~ v1_relat_1(sK3(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK3(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK3(X0,X1)))
      | ~ v1_funct_1(sK3(X0,X1))
      | ~ v1_relat_1(sK3(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f71,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK3(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f231,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ r2_hidden(X28,k2_relat_1(sK3(X29,X30)))
      | ~ r2_hidden(X28,X31)
      | k1_funct_1(k6_relat_1(X31),X28) = X30 ) ),
    inference(resolution,[],[f223,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK3(X0,X1)))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f142,f113])).

fof(f113,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK6(sK3(X2,X3),X4),X2)
      | ~ r2_hidden(X4,k2_relat_1(sK3(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f112,f55])).

fof(f112,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK6(sK3(X2,X3),X4),X2)
      | ~ r2_hidden(X4,k2_relat_1(sK3(X2,X3)))
      | ~ v1_relat_1(sK3(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f108,f56])).

fof(f108,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK6(sK3(X2,X3),X4),X2)
      | ~ r2_hidden(X4,k2_relat_1(sK3(X2,X3)))
      | ~ v1_funct_1(sK3(X2,X3))
      | ~ v1_relat_1(sK3(X2,X3)) ) ),
    inference(superposition,[],[f73,f57])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK3(X0,X1)))
      | ~ r2_hidden(sK6(sK3(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f141,f55])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK3(X0,X1)))
      | ~ v1_relat_1(sK3(X0,X1))
      | ~ r2_hidden(sK6(sK3(X0,X1),X2),X0) ) ),
    inference(subsumption_resolution,[],[f136,f56])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK3(X0,X1)))
      | ~ v1_funct_1(sK3(X0,X1))
      | ~ v1_relat_1(sK3(X0,X1))
      | ~ r2_hidden(sK6(sK3(X0,X1),X2),X0) ) ),
    inference(superposition,[],[f72,f58])).

fof(f72,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(k6_relat_1(X0),X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f222,f62])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(k6_relat_1(X0),X1),X2)
      | ~ r2_hidden(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f217,f60])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(k6_relat_1(X0),X1),X2)
      | ~ r2_hidden(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f216,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
      | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1) ) ),
    inference(subsumption_resolution,[],[f215,f60])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
      | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f214,f60])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
      | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f213,f61])).

fof(f61,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
      | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(f963,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f962,f62])).

fof(f962,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f961,f60])).

fof(f961,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f960,f61])).

fof(f960,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f954])).

fof(f954,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f59,f51])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f92,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_4
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f93,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f47,f90])).

fof(f47,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,X1)
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f88,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f46,f85])).

fof(f46,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f44,f75])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (32196)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.46  % (32188)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (32179)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (32172)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (32185)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (32180)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (32176)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (32173)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (32174)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32175)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (32189)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (32194)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (32201)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (32177)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (32186)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (32199)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32193)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (32200)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (32191)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (32178)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (32182)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (32192)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (32194)Refutation not found, incomplete strategy% (32194)------------------------------
% 0.21/0.54  % (32194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32194)Memory used [KB]: 10746
% 0.21/0.54  % (32194)Time elapsed: 0.096 s
% 0.21/0.54  % (32194)------------------------------
% 0.21/0.54  % (32194)------------------------------
% 0.21/0.54  % (32182)Refutation not found, incomplete strategy% (32182)------------------------------
% 0.21/0.54  % (32182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32182)Memory used [KB]: 10618
% 0.21/0.54  % (32182)Time elapsed: 0.129 s
% 0.21/0.54  % (32182)------------------------------
% 0.21/0.54  % (32182)------------------------------
% 0.21/0.54  % (32190)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (32184)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (32183)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32195)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (32198)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (32189)Refutation not found, incomplete strategy% (32189)------------------------------
% 0.21/0.55  % (32189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32197)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (32189)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32189)Memory used [KB]: 10618
% 0.21/0.55  % (32189)Time elapsed: 0.140 s
% 0.21/0.55  % (32189)------------------------------
% 0.21/0.55  % (32189)------------------------------
% 0.21/0.55  % (32187)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (32181)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.12/0.68  % (32204)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.12/0.69  % (32202)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.70  % (32203)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.24/0.82  % (32177)Time limit reached!
% 3.24/0.82  % (32177)------------------------------
% 3.24/0.82  % (32177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.24/0.83  % (32177)Termination reason: Time limit
% 3.24/0.83  % (32177)Termination phase: Saturation
% 3.24/0.83  
% 3.24/0.83  % (32177)Memory used [KB]: 9338
% 3.24/0.83  % (32177)Time elapsed: 0.400 s
% 3.24/0.83  % (32177)------------------------------
% 3.24/0.83  % (32177)------------------------------
% 4.07/0.91  % (32184)Time limit reached!
% 4.07/0.91  % (32184)------------------------------
% 4.07/0.91  % (32184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.91  % (32172)Time limit reached!
% 4.07/0.91  % (32172)------------------------------
% 4.07/0.91  % (32172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.92  % (32184)Termination reason: Time limit
% 4.35/0.92  % (32184)Termination phase: Saturation
% 4.35/0.92  
% 4.35/0.92  % (32184)Memory used [KB]: 8699
% 4.35/0.92  % (32184)Time elapsed: 0.500 s
% 4.35/0.92  % (32184)------------------------------
% 4.35/0.92  % (32184)------------------------------
% 4.41/0.93  % (32172)Termination reason: Time limit
% 4.41/0.93  % (32172)Termination phase: Saturation
% 4.41/0.93  
% 4.41/0.93  % (32172)Memory used [KB]: 4861
% 4.41/0.93  % (32172)Time elapsed: 0.500 s
% 4.41/0.93  % (32172)------------------------------
% 4.41/0.93  % (32172)------------------------------
% 4.41/0.95  % (32173)Time limit reached!
% 4.41/0.95  % (32173)------------------------------
% 4.41/0.95  % (32173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.95  % (32173)Termination reason: Time limit
% 4.41/0.95  
% 4.41/0.95  % (32173)Memory used [KB]: 9466
% 4.41/0.95  % (32173)Time elapsed: 0.536 s
% 4.41/0.95  % (32173)------------------------------
% 4.41/0.95  % (32173)------------------------------
% 4.41/0.97  % (32206)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.41/1.01  % (32179)Time limit reached!
% 4.41/1.01  % (32179)------------------------------
% 4.41/1.01  % (32179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/1.01  % (32179)Termination reason: Time limit
% 4.41/1.01  % (32179)Termination phase: Saturation
% 4.41/1.01  
% 4.41/1.01  % (32179)Memory used [KB]: 11897
% 4.41/1.01  % (32179)Time elapsed: 0.600 s
% 4.41/1.01  % (32179)------------------------------
% 4.41/1.01  % (32179)------------------------------
% 4.97/1.02  % (32188)Time limit reached!
% 4.97/1.02  % (32188)------------------------------
% 4.97/1.02  % (32188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.03  % (32200)Time limit reached!
% 4.97/1.03  % (32200)------------------------------
% 4.97/1.03  % (32200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.03  % (32200)Termination reason: Time limit
% 4.97/1.03  % (32200)Termination phase: Saturation
% 4.97/1.03  
% 4.97/1.03  % (32200)Memory used [KB]: 8955
% 4.97/1.03  % (32200)Time elapsed: 0.600 s
% 4.97/1.03  % (32200)------------------------------
% 4.97/1.03  % (32200)------------------------------
% 4.97/1.03  % (32188)Termination reason: Time limit
% 4.97/1.03  
% 4.97/1.03  % (32188)Memory used [KB]: 21236
% 4.97/1.03  % (32188)Time elapsed: 0.608 s
% 4.97/1.03  % (32188)------------------------------
% 4.97/1.03  % (32188)------------------------------
% 4.97/1.05  % (32208)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.97/1.05  % (32207)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.46/1.08  % (32209)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.46/1.13  % (32210)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.46/1.16  % (32211)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.46/1.16  % (32212)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.46/1.17  % (32207)Refutation found. Thanks to Tanya!
% 5.46/1.17  % SZS status Theorem for theBenchmark
% 5.46/1.17  % SZS output start Proof for theBenchmark
% 5.46/1.17  fof(f1700,plain,(
% 5.46/1.17    $false),
% 5.46/1.17    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f1697])).
% 5.46/1.17  fof(f1697,plain,(
% 5.46/1.17    ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4),
% 5.46/1.17    inference(avatar_contradiction_clause,[],[f1696])).
% 5.46/1.17  fof(f1696,plain,(
% 5.46/1.17    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4)),
% 5.46/1.17    inference(subsumption_resolution,[],[f1695,f77])).
% 5.46/1.17  fof(f77,plain,(
% 5.46/1.17    v1_relat_1(sK2) | ~spl7_1),
% 5.46/1.17    inference(avatar_component_clause,[],[f75])).
% 5.46/1.17  fof(f75,plain,(
% 5.46/1.17    spl7_1 <=> v1_relat_1(sK2)),
% 5.46/1.17    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 5.46/1.17  fof(f1695,plain,(
% 5.46/1.17    ~v1_relat_1(sK2) | (~spl7_2 | ~spl7_3 | spl7_4)),
% 5.46/1.17    inference(subsumption_resolution,[],[f1694,f82])).
% 5.46/1.17  fof(f82,plain,(
% 5.46/1.17    v1_funct_1(sK2) | ~spl7_2),
% 5.46/1.17    inference(avatar_component_clause,[],[f80])).
% 5.46/1.17  fof(f80,plain,(
% 5.46/1.17    spl7_2 <=> v1_funct_1(sK2)),
% 5.46/1.17    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 5.46/1.17  fof(f1694,plain,(
% 5.46/1.17    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | spl7_4)),
% 5.46/1.17    inference(subsumption_resolution,[],[f1688,f87])).
% 5.46/1.17  fof(f87,plain,(
% 5.46/1.17    r2_hidden(sK0,sK1) | ~spl7_3),
% 5.46/1.17    inference(avatar_component_clause,[],[f85])).
% 5.46/1.17  fof(f85,plain,(
% 5.46/1.17    spl7_3 <=> r2_hidden(sK0,sK1)),
% 5.46/1.17    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 5.46/1.17  fof(f1688,plain,(
% 5.46/1.17    ~r2_hidden(sK0,sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_4),
% 5.46/1.17    inference(trivial_inequality_removal,[],[f1679])).
% 5.46/1.17  fof(f1679,plain,(
% 5.46/1.17    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_4),
% 5.46/1.17    inference(superposition,[],[f92,f1542])).
% 5.46/1.17  fof(f1542,plain,(
% 5.46/1.17    ( ! [X21,X22,X20] : (k1_funct_1(k7_relat_1(X22,X20),X21) = k1_funct_1(X22,X21) | ~r2_hidden(X21,X20) | ~v1_funct_1(X22) | ~v1_relat_1(X22)) )),
% 5.46/1.17    inference(duplicate_literal_removal,[],[f1499])).
% 5.46/1.17  fof(f1499,plain,(
% 5.46/1.17    ( ! [X21,X22,X20] : (k1_funct_1(k7_relat_1(X22,X20),X21) = k1_funct_1(X22,X21) | ~r2_hidden(X21,X20) | ~v1_funct_1(X22) | ~v1_relat_1(X22) | ~r2_hidden(X21,X20)) )),
% 5.46/1.17    inference(superposition,[],[f963,f328])).
% 5.46/1.17  fof(f328,plain,(
% 5.46/1.17    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 5.46/1.17    inference(condensation,[],[f320])).
% 5.46/1.17  fof(f320,plain,(
% 5.46/1.17    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X2,X3)) )),
% 5.46/1.17    inference(resolution,[],[f231,f99])).
% 5.46/1.17  fof(f99,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK3(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 5.46/1.17    inference(duplicate_literal_removal,[],[f98])).
% 5.46/1.17  fof(f98,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X1,k2_relat_1(sK3(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 5.46/1.17    inference(forward_demodulation,[],[f97,f57])).
% 5.46/1.17  fof(f57,plain,(
% 5.46/1.17    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 5.46/1.17    inference(cnf_transformation,[],[f37])).
% 5.46/1.17  fof(f37,plain,(
% 5.46/1.17    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 5.46/1.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f36])).
% 5.46/1.17  fof(f36,plain,(
% 5.46/1.17    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 5.46/1.17    introduced(choice_axiom,[])).
% 5.46/1.17  fof(f25,plain,(
% 5.46/1.17    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 5.46/1.17    inference(ennf_transformation,[],[f14])).
% 5.46/1.17  fof(f14,axiom,(
% 5.46/1.17    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 5.46/1.17  fof(f97,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK3(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK3(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f96,f55])).
% 5.46/1.17  fof(f55,plain,(
% 5.46/1.17    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 5.46/1.17    inference(cnf_transformation,[],[f37])).
% 5.46/1.17  fof(f96,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK3(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK3(X0,X1))) | ~v1_relat_1(sK3(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f94,f56])).
% 5.46/1.17  fof(f56,plain,(
% 5.46/1.17    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 5.46/1.17    inference(cnf_transformation,[],[f37])).
% 5.46/1.17  fof(f94,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK3(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK3(X0,X1))) | ~v1_funct_1(sK3(X0,X1)) | ~v1_relat_1(sK3(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 5.46/1.17    inference(superposition,[],[f71,f58])).
% 5.46/1.17  fof(f58,plain,(
% 5.46/1.17    ( ! [X0,X3,X1] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f37])).
% 5.46/1.17  fof(f71,plain,(
% 5.46/1.17    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.46/1.17    inference(equality_resolution,[],[f70])).
% 5.46/1.17  fof(f70,plain,(
% 5.46/1.17    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.46/1.17    inference(equality_resolution,[],[f66])).
% 5.46/1.17  fof(f66,plain,(
% 5.46/1.17    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f43])).
% 5.46/1.17  fof(f43,plain,(
% 5.46/1.17    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.46/1.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).
% 5.46/1.17  fof(f40,plain,(
% 5.46/1.17    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 5.46/1.17    introduced(choice_axiom,[])).
% 5.46/1.17  fof(f41,plain,(
% 5.46/1.17    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 5.46/1.17    introduced(choice_axiom,[])).
% 5.46/1.17  fof(f42,plain,(
% 5.46/1.17    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 5.46/1.17    introduced(choice_axiom,[])).
% 5.46/1.17  fof(f39,plain,(
% 5.46/1.17    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.46/1.17    inference(rectify,[],[f38])).
% 5.46/1.17  fof(f38,plain,(
% 5.46/1.17    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.46/1.17    inference(nnf_transformation,[],[f29])).
% 5.46/1.17  fof(f29,plain,(
% 5.46/1.17    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.46/1.17    inference(flattening,[],[f28])).
% 5.46/1.17  fof(f28,plain,(
% 5.46/1.17    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.46/1.17    inference(ennf_transformation,[],[f12])).
% 5.46/1.17  fof(f12,axiom,(
% 5.46/1.17    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 5.46/1.17  fof(f231,plain,(
% 5.46/1.17    ( ! [X30,X28,X31,X29] : (~r2_hidden(X28,k2_relat_1(sK3(X29,X30))) | ~r2_hidden(X28,X31) | k1_funct_1(k6_relat_1(X31),X28) = X30) )),
% 5.46/1.17    inference(resolution,[],[f223,f143])).
% 5.46/1.17  fof(f143,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK3(X0,X1))) | X1 = X2) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f142,f113])).
% 5.46/1.17  fof(f113,plain,(
% 5.46/1.17    ( ! [X4,X2,X3] : (r2_hidden(sK6(sK3(X2,X3),X4),X2) | ~r2_hidden(X4,k2_relat_1(sK3(X2,X3)))) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f112,f55])).
% 5.46/1.17  fof(f112,plain,(
% 5.46/1.17    ( ! [X4,X2,X3] : (r2_hidden(sK6(sK3(X2,X3),X4),X2) | ~r2_hidden(X4,k2_relat_1(sK3(X2,X3))) | ~v1_relat_1(sK3(X2,X3))) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f108,f56])).
% 5.46/1.17  fof(f108,plain,(
% 5.46/1.17    ( ! [X4,X2,X3] : (r2_hidden(sK6(sK3(X2,X3),X4),X2) | ~r2_hidden(X4,k2_relat_1(sK3(X2,X3))) | ~v1_funct_1(sK3(X2,X3)) | ~v1_relat_1(sK3(X2,X3))) )),
% 5.46/1.17    inference(superposition,[],[f73,f57])).
% 5.46/1.17  fof(f73,plain,(
% 5.46/1.17    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.46/1.17    inference(equality_resolution,[],[f64])).
% 5.46/1.17  fof(f64,plain,(
% 5.46/1.17    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f43])).
% 5.46/1.17  fof(f142,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK3(X0,X1))) | ~r2_hidden(sK6(sK3(X0,X1),X2),X0)) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f141,f55])).
% 5.46/1.17  fof(f141,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK3(X0,X1))) | ~v1_relat_1(sK3(X0,X1)) | ~r2_hidden(sK6(sK3(X0,X1),X2),X0)) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f136,f56])).
% 5.46/1.17  fof(f136,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X2,k2_relat_1(sK3(X0,X1))) | ~v1_funct_1(sK3(X0,X1)) | ~v1_relat_1(sK3(X0,X1)) | ~r2_hidden(sK6(sK3(X0,X1),X2),X0)) )),
% 5.46/1.17    inference(superposition,[],[f72,f58])).
% 5.46/1.17  fof(f72,plain,(
% 5.46/1.17    ( ! [X0,X5] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.46/1.17    inference(equality_resolution,[],[f65])).
% 5.46/1.17  fof(f65,plain,(
% 5.46/1.17    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f43])).
% 5.46/1.17  fof(f223,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(k6_relat_1(X0),X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 5.46/1.17    inference(forward_demodulation,[],[f222,f62])).
% 5.46/1.17  fof(f62,plain,(
% 5.46/1.17    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 5.46/1.17    inference(cnf_transformation,[],[f9])).
% 5.46/1.17  fof(f9,axiom,(
% 5.46/1.17    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 5.46/1.17  fof(f222,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(k6_relat_1(X0),X1),X2) | ~r2_hidden(X1,k1_relat_1(k6_relat_1(X2))) | ~r2_hidden(X1,X0)) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f217,f60])).
% 5.46/1.17  fof(f60,plain,(
% 5.46/1.17    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 5.46/1.17    inference(cnf_transformation,[],[f13])).
% 5.46/1.17  fof(f13,axiom,(
% 5.46/1.17    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 5.46/1.17  fof(f217,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(k6_relat_1(X0),X1),X2) | ~r2_hidden(X1,k1_relat_1(k6_relat_1(X2))) | ~r2_hidden(X1,X0) | ~v1_relat_1(k6_relat_1(X2))) )),
% 5.46/1.17    inference(resolution,[],[f216,f50])).
% 5.46/1.17  fof(f50,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f33])).
% 5.46/1.17  fof(f33,plain,(
% 5.46/1.17    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 5.46/1.17    inference(flattening,[],[f32])).
% 5.46/1.17  fof(f32,plain,(
% 5.46/1.17    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 5.46/1.17    inference(nnf_transformation,[],[f21])).
% 5.46/1.17  fof(f21,plain,(
% 5.46/1.17    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 5.46/1.17    inference(ennf_transformation,[],[f10])).
% 5.46/1.17  fof(f10,axiom,(
% 5.46/1.17    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 5.46/1.17  fof(f216,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1)) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f215,f60])).
% 5.46/1.17  fof(f215,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f214,f60])).
% 5.46/1.17  fof(f214,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f213,f61])).
% 5.46/1.17  fof(f61,plain,(
% 5.46/1.17    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 5.46/1.17    inference(cnf_transformation,[],[f13])).
% 5.46/1.17  fof(f213,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) | r2_hidden(k1_funct_1(k6_relat_1(X0),X2),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 5.46/1.17    inference(superposition,[],[f53,f51])).
% 5.46/1.17  fof(f51,plain,(
% 5.46/1.17    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f22])).
% 5.46/1.17  fof(f22,plain,(
% 5.46/1.17    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 5.46/1.17    inference(ennf_transformation,[],[f11])).
% 5.46/1.17  fof(f11,axiom,(
% 5.46/1.17    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 5.46/1.17  fof(f53,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | r2_hidden(k1_funct_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f35])).
% 5.46/1.17  fof(f35,plain,(
% 5.46/1.17    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.46/1.17    inference(flattening,[],[f34])).
% 5.46/1.17  fof(f34,plain,(
% 5.46/1.17    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.46/1.17    inference(nnf_transformation,[],[f24])).
% 5.46/1.17  fof(f24,plain,(
% 5.46/1.17    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.46/1.17    inference(flattening,[],[f23])).
% 5.46/1.17  fof(f23,plain,(
% 5.46/1.17    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 5.46/1.17    inference(ennf_transformation,[],[f16])).
% 5.46/1.17  fof(f16,axiom,(
% 5.46/1.17    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).
% 5.46/1.17  fof(f963,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.46/1.17    inference(forward_demodulation,[],[f962,f62])).
% 5.46/1.17  fof(f962,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f961,f60])).
% 5.46/1.17  fof(f961,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 5.46/1.17    inference(subsumption_resolution,[],[f960,f61])).
% 5.46/1.17  fof(f960,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 5.46/1.17    inference(duplicate_literal_removal,[],[f954])).
% 5.46/1.17  fof(f954,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2)) = k1_funct_1(k7_relat_1(X1,X0),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 5.46/1.17    inference(superposition,[],[f59,f51])).
% 5.46/1.17  fof(f59,plain,(
% 5.46/1.17    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.46/1.17    inference(cnf_transformation,[],[f27])).
% 5.46/1.17  fof(f27,plain,(
% 5.46/1.17    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.46/1.17    inference(flattening,[],[f26])).
% 5.46/1.17  fof(f26,plain,(
% 5.46/1.17    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 5.46/1.17    inference(ennf_transformation,[],[f15])).
% 5.46/1.17  fof(f15,axiom,(
% 5.46/1.17    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 5.46/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 5.46/1.17  fof(f92,plain,(
% 5.46/1.17    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) | spl7_4),
% 5.46/1.17    inference(avatar_component_clause,[],[f90])).
% 5.46/1.17  fof(f90,plain,(
% 5.46/1.17    spl7_4 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 5.46/1.17    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 5.46/1.17  fof(f93,plain,(
% 5.46/1.17    ~spl7_4),
% 5.46/1.17    inference(avatar_split_clause,[],[f47,f90])).
% 5.46/1.17  fof(f47,plain,(
% 5.46/1.17    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 5.46/1.17    inference(cnf_transformation,[],[f31])).
% 5.46/1.17  fof(f31,plain,(
% 5.46/1.17    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 5.46/1.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30])).
% 5.46/1.17  fof(f30,plain,(
% 5.46/1.17    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 5.46/1.17    introduced(choice_axiom,[])).
% 5.46/1.17  fof(f20,plain,(
% 5.46/1.17    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 5.46/1.17    inference(flattening,[],[f19])).
% 6.43/1.19  fof(f19,plain,(
% 6.43/1.19    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 6.43/1.19    inference(ennf_transformation,[],[f18])).
% 6.43/1.19  fof(f18,negated_conjecture,(
% 6.43/1.19    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 6.43/1.19    inference(negated_conjecture,[],[f17])).
% 6.43/1.19  fof(f17,conjecture,(
% 6.43/1.19    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 6.43/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).
% 6.43/1.19  fof(f88,plain,(
% 6.43/1.19    spl7_3),
% 6.43/1.19    inference(avatar_split_clause,[],[f46,f85])).
% 6.43/1.19  fof(f46,plain,(
% 6.43/1.19    r2_hidden(sK0,sK1)),
% 6.43/1.19    inference(cnf_transformation,[],[f31])).
% 6.43/1.19  fof(f83,plain,(
% 6.43/1.19    spl7_2),
% 6.43/1.19    inference(avatar_split_clause,[],[f45,f80])).
% 6.43/1.19  fof(f45,plain,(
% 6.43/1.19    v1_funct_1(sK2)),
% 6.43/1.19    inference(cnf_transformation,[],[f31])).
% 6.43/1.19  fof(f78,plain,(
% 6.43/1.19    spl7_1),
% 6.43/1.19    inference(avatar_split_clause,[],[f44,f75])).
% 6.43/1.19  fof(f44,plain,(
% 6.43/1.19    v1_relat_1(sK2)),
% 6.43/1.19    inference(cnf_transformation,[],[f31])).
% 6.43/1.19  % SZS output end Proof for theBenchmark
% 6.43/1.19  % (32207)------------------------------
% 6.43/1.19  % (32207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.43/1.19  % (32207)Termination reason: Refutation
% 6.43/1.19  
% 6.43/1.19  % (32207)Memory used [KB]: 11897
% 6.43/1.19  % (32207)Time elapsed: 0.214 s
% 6.43/1.19  % (32207)------------------------------
% 6.43/1.19  % (32207)------------------------------
% 6.43/1.19  % (32171)Success in time 0.827 s
%------------------------------------------------------------------------------
