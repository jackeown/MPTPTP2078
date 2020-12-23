%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0802+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 427 expanded)
%              Number of leaves         :    6 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          :  356 (3322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6605,plain,(
    $false ),
    inference(global_subsumption,[],[f6582,f6587,f6592,f6597,f6604])).

fof(f6604,plain,
    ( ~ v1_wellord1(sK23)
    | ~ v6_relat_2(sK23)
    | ~ v4_relat_2(sK23)
    | ~ v8_relat_2(sK23) ),
    inference(subsumption_resolution,[],[f6603,f3241])).

fof(f3241,plain,(
    v1_relat_1(sK23) ),
    inference(cnf_transformation,[],[f2439])).

fof(f2439,plain,
    ( ~ v2_wellord1(sK23)
    & r3_wellord1(sK22,sK23,sK24)
    & v2_wellord1(sK22)
    & v1_funct_1(sK24)
    & v1_relat_1(sK24)
    & v1_relat_1(sK23)
    & v1_relat_1(sK22) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23,sK24])],[f1223,f2438,f2437,f2436])).

fof(f2436,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_wellord1(X1)
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(sK22,X1,X2)
              & v2_wellord1(sK22)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f2437,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_wellord1(X1)
            & r3_wellord1(sK22,X1,X2)
            & v2_wellord1(sK22)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ v2_wellord1(sK23)
          & r3_wellord1(sK22,sK23,X2)
          & v2_wellord1(sK22)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK23) ) ),
    introduced(choice_axiom,[])).

fof(f2438,plain,
    ( ? [X2] :
        ( ~ v2_wellord1(sK23)
        & r3_wellord1(sK22,sK23,X2)
        & v2_wellord1(sK22)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ v2_wellord1(sK23)
      & r3_wellord1(sK22,sK23,sK24)
      & v2_wellord1(sK22)
      & v1_funct_1(sK24)
      & v1_relat_1(sK24) ) ),
    introduced(choice_axiom,[])).

fof(f1223,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1222])).

fof(f1222,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1193])).

fof(f1193,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => v2_wellord1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1192])).

fof(f1192,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

fof(f6603,plain,
    ( ~ v1_wellord1(sK23)
    | ~ v6_relat_2(sK23)
    | ~ v4_relat_2(sK23)
    | ~ v8_relat_2(sK23)
    | ~ v1_relat_1(sK23) ),
    inference(subsumption_resolution,[],[f6602,f3246])).

fof(f3246,plain,(
    ~ v2_wellord1(sK23) ),
    inference(cnf_transformation,[],[f2439])).

fof(f6602,plain,
    ( ~ v1_wellord1(sK23)
    | ~ v6_relat_2(sK23)
    | ~ v4_relat_2(sK23)
    | ~ v8_relat_2(sK23)
    | v2_wellord1(sK23)
    | ~ v1_relat_1(sK23) ),
    inference(resolution,[],[f6577,f3470])).

fof(f3470,plain,(
    ! [X0] :
      ( ~ v1_relat_2(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2493])).

fof(f2493,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2492])).

fof(f2492,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1323])).

fof(f1323,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f6577,plain,(
    v1_relat_2(sK23) ),
    inference(subsumption_resolution,[],[f6576,f3240])).

fof(f3240,plain,(
    v1_relat_1(sK22) ),
    inference(cnf_transformation,[],[f2439])).

fof(f6576,plain,
    ( v1_relat_2(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6575,f3241])).

fof(f6575,plain,
    ( v1_relat_2(sK23)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6574,f3242])).

fof(f3242,plain,(
    v1_relat_1(sK24) ),
    inference(cnf_transformation,[],[f2439])).

fof(f6574,plain,
    ( v1_relat_2(sK23)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6573,f3243])).

fof(f3243,plain,(
    v1_funct_1(sK24) ),
    inference(cnf_transformation,[],[f2439])).

fof(f6573,plain,
    ( v1_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6567,f6559])).

fof(f6559,plain,(
    v1_relat_2(sK22) ),
    inference(subsumption_resolution,[],[f6554,f3240])).

fof(f6554,plain,
    ( v1_relat_2(sK22)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3244,f3465])).

fof(f3465,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2493])).

fof(f3244,plain,(
    v2_wellord1(sK22) ),
    inference(cnf_transformation,[],[f2439])).

fof(f6567,plain,
    ( ~ v1_relat_2(sK22)
    | v1_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3245,f3544])).

fof(f3544,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_2(X0)
      | v1_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1395,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1394])).

fof(f1394,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1191])).

fof(f1191,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

fof(f3245,plain,(
    r3_wellord1(sK22,sK23,sK24) ),
    inference(cnf_transformation,[],[f2439])).

fof(f6597,plain,(
    v1_wellord1(sK23) ),
    inference(subsumption_resolution,[],[f6596,f3240])).

fof(f6596,plain,
    ( v1_wellord1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6595,f3241])).

fof(f6595,plain,
    ( v1_wellord1(sK23)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6594,f3242])).

fof(f6594,plain,
    ( v1_wellord1(sK23)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6593,f3243])).

fof(f6593,plain,
    ( v1_wellord1(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6571,f6563])).

fof(f6563,plain,(
    v1_wellord1(sK22) ),
    inference(subsumption_resolution,[],[f6558,f3240])).

fof(f6558,plain,
    ( v1_wellord1(sK22)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3244,f3469])).

fof(f3469,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2493])).

fof(f6571,plain,
    ( ~ v1_wellord1(sK22)
    | v1_wellord1(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3245,f3548])).

fof(f3548,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_wellord1(X0)
      | v1_wellord1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1395])).

fof(f6592,plain,(
    v4_relat_2(sK23) ),
    inference(subsumption_resolution,[],[f6591,f3240])).

fof(f6591,plain,
    ( v4_relat_2(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6590,f3241])).

fof(f6590,plain,
    ( v4_relat_2(sK23)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6589,f3242])).

fof(f6589,plain,
    ( v4_relat_2(sK23)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6588,f3243])).

fof(f6588,plain,
    ( v4_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6570,f6561])).

fof(f6561,plain,(
    v4_relat_2(sK22) ),
    inference(subsumption_resolution,[],[f6556,f3240])).

fof(f6556,plain,
    ( v4_relat_2(sK22)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3244,f3467])).

fof(f3467,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2493])).

fof(f6570,plain,
    ( ~ v4_relat_2(sK22)
    | v4_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3245,f3547])).

fof(f3547,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v4_relat_2(X0)
      | v4_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1395])).

fof(f6587,plain,(
    v6_relat_2(sK23) ),
    inference(subsumption_resolution,[],[f6586,f3240])).

fof(f6586,plain,
    ( v6_relat_2(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6585,f3241])).

fof(f6585,plain,
    ( v6_relat_2(sK23)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6584,f3242])).

fof(f6584,plain,
    ( v6_relat_2(sK23)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6583,f3243])).

fof(f6583,plain,
    ( v6_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6569,f6562])).

fof(f6562,plain,(
    v6_relat_2(sK22) ),
    inference(subsumption_resolution,[],[f6557,f3240])).

fof(f6557,plain,
    ( v6_relat_2(sK22)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3244,f3468])).

fof(f3468,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2493])).

fof(f6569,plain,
    ( ~ v6_relat_2(sK22)
    | v6_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3245,f3546])).

fof(f3546,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v6_relat_2(X0)
      | v6_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1395])).

fof(f6582,plain,(
    v8_relat_2(sK23) ),
    inference(subsumption_resolution,[],[f6581,f3240])).

fof(f6581,plain,
    ( v8_relat_2(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6580,f3241])).

fof(f6580,plain,
    ( v8_relat_2(sK23)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6579,f3242])).

fof(f6579,plain,
    ( v8_relat_2(sK23)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6578,f3243])).

fof(f6578,plain,
    ( v8_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(subsumption_resolution,[],[f6568,f6560])).

fof(f6560,plain,(
    v8_relat_2(sK22) ),
    inference(subsumption_resolution,[],[f6555,f3240])).

fof(f6555,plain,
    ( v8_relat_2(sK22)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3244,f3466])).

fof(f3466,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2493])).

fof(f6568,plain,
    ( ~ v8_relat_2(sK22)
    | v8_relat_2(sK23)
    | ~ v1_funct_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ v1_relat_1(sK23)
    | ~ v1_relat_1(sK22) ),
    inference(resolution,[],[f3245,f3545])).

fof(f3545,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v8_relat_2(X0)
      | v8_relat_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1395])).
%------------------------------------------------------------------------------
