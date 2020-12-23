%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0798+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 183 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :   20
%              Number of atoms          :  238 ( 850 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6988,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6972,f6979,f6987])).

fof(f6987,plain,(
    spl295_2 ),
    inference(avatar_contradiction_clause,[],[f6986])).

fof(f6986,plain,
    ( $false
    | spl295_2 ),
    inference(subsumption_resolution,[],[f6985,f3179])).

fof(f3179,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f2401])).

fof(f2401,plain,
    ( ~ r4_wellord1(sK7,sK6)
    & r4_wellord1(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f1219,f2400,f2399])).

fof(f2399,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r4_wellord1(X1,X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r4_wellord1(X1,sK6)
          & r4_wellord1(sK6,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f2400,plain,
    ( ? [X1] :
        ( ~ r4_wellord1(X1,sK6)
        & r4_wellord1(sK6,X1)
        & v1_relat_1(X1) )
   => ( ~ r4_wellord1(sK7,sK6)
      & r4_wellord1(sK6,sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f1219,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1218])).

fof(f1218,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1189])).

fof(f1189,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r4_wellord1(X0,X1)
             => r4_wellord1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1188])).

fof(f1188,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f6985,plain,
    ( ~ v1_relat_1(sK6)
    | spl295_2 ),
    inference(subsumption_resolution,[],[f6984,f3180])).

fof(f3180,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f2401])).

fof(f6984,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | spl295_2 ),
    inference(subsumption_resolution,[],[f6981,f3181])).

fof(f3181,plain,(
    r4_wellord1(sK6,sK7) ),
    inference(cnf_transformation,[],[f2401])).

fof(f6981,plain,
    ( ~ r4_wellord1(sK6,sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | spl295_2 ),
    inference(resolution,[],[f6971,f3451])).

fof(f3451,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK34(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2472])).

fof(f2472,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK34(X0,X1))
                & v1_funct_1(sK34(X0,X1))
                & v1_relat_1(sK34(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34])],[f2470,f2471])).

fof(f2471,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK34(X0,X1))
        & v1_funct_1(sK34(X0,X1))
        & v1_relat_1(sK34(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2470,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X3] :
                  ( r3_wellord1(X0,X1,X3)
                  & v1_funct_1(X3)
                  & v1_relat_1(X3) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2469])).

fof(f2469,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X2] :
                  ( r3_wellord1(X0,X1,X2)
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1364])).

fof(f1364,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1138])).

fof(f1138,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(f6971,plain,
    ( ~ v1_relat_1(sK34(sK6,sK7))
    | spl295_2 ),
    inference(avatar_component_clause,[],[f6969])).

fof(f6969,plain,
    ( spl295_2
  <=> v1_relat_1(sK34(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl295_2])])).

fof(f6979,plain,(
    spl295_1 ),
    inference(avatar_contradiction_clause,[],[f6978])).

fof(f6978,plain,
    ( $false
    | spl295_1 ),
    inference(subsumption_resolution,[],[f6977,f3179])).

fof(f6977,plain,
    ( ~ v1_relat_1(sK6)
    | spl295_1 ),
    inference(subsumption_resolution,[],[f6976,f3180])).

fof(f6976,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | spl295_1 ),
    inference(subsumption_resolution,[],[f6974,f3181])).

fof(f6974,plain,
    ( ~ r4_wellord1(sK6,sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | spl295_1 ),
    inference(resolution,[],[f6967,f3452])).

fof(f3452,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK34(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2472])).

fof(f6967,plain,
    ( ~ v1_funct_1(sK34(sK6,sK7))
    | spl295_1 ),
    inference(avatar_component_clause,[],[f6965])).

fof(f6965,plain,
    ( spl295_1
  <=> v1_funct_1(sK34(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl295_1])])).

fof(f6972,plain,
    ( ~ spl295_1
    | ~ spl295_2 ),
    inference(avatar_split_clause,[],[f6963,f6969,f6965])).

fof(f6963,plain,
    ( ~ v1_relat_1(sK34(sK6,sK7))
    | ~ v1_funct_1(sK34(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f6962,f3179])).

fof(f6962,plain,
    ( ~ v1_relat_1(sK34(sK6,sK7))
    | ~ v1_funct_1(sK34(sK6,sK7))
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f6961,f3180])).

fof(f6961,plain,
    ( ~ v1_relat_1(sK34(sK6,sK7))
    | ~ v1_funct_1(sK34(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f6959,f3181])).

fof(f6959,plain,
    ( ~ v1_relat_1(sK34(sK6,sK7))
    | ~ v1_funct_1(sK34(sK6,sK7))
    | ~ r4_wellord1(sK6,sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f6952,f3453])).

fof(f3453,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK34(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2472])).

fof(f6952,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK6,sK7,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f6951,f3589])).

fof(f3589,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1457])).

fof(f1457,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1456])).

fof(f1456,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f908])).

fof(f908,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f6951,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(sK6,sK7,X0)
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f6950])).

fof(f6950,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(sK6,sK7,X0)
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f3590,f6937])).

fof(f6937,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(sK6,sK7,X0)
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f6936,f3179])).

fof(f6936,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK6,sK7,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f6935,f3180])).

fof(f6935,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK6,sK7,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK7)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f3476,f6933])).

fof(f6933,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK7,sK6,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f6932,f3180])).

fof(f6932,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK7,sK6,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK7) ) ),
    inference(subsumption_resolution,[],[f6931,f3179])).

fof(f6931,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK7,sK6,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK6)
      | ~ v1_relat_1(sK7) ) ),
    inference(resolution,[],[f3454,f3182])).

fof(f3182,plain,(
    ~ r4_wellord1(sK7,sK6) ),
    inference(cnf_transformation,[],[f2401])).

fof(f3454,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2472])).

fof(f3476,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X1,X0,k2_funct_1(X2))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1383])).

fof(f1383,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1382])).

fof(f1382,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1187])).

fof(f1187,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_wellord1)).

fof(f3590,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1457])).
%------------------------------------------------------------------------------
