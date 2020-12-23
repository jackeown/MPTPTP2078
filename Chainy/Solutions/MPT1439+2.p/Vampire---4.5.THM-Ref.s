%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1439+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 309 expanded)
%              Number of leaves         :    7 ( 127 expanded)
%              Depth                    :    8
%              Number of atoms          :  224 (3656 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2982,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2977,f2954])).

fof(f2954,plain,(
    ~ r4_wellord1(k8_filter_1(sK3),k8_filter_1(sK5)) ),
    inference(unit_resulting_resolution,[],[f2843,f2844,f2845,f2849,f2850,f2851,f2854,f2858])).

fof(f2858,plain,(
    ! [X0,X1] :
      ( r1_filter_1(X0,X1)
      | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f2791,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_filter_1(X0,X1)
              | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
            & ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
              | ~ r1_filter_1(X0,X1) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2738])).

% (25072)Termination reason: Refutation not found, incomplete strategy

% (25072)Memory used [KB]: 9722
% (25072)Time elapsed: 0.164 s
% (25072)------------------------------
% (25072)------------------------------
fof(f2738,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2737])).

fof(f2737,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2605])).

fof(f2605,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_filter_1)).

fof(f2854,plain,(
    ~ r1_filter_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2790,plain,
    ( ~ r1_filter_1(sK3,sK5)
    & r1_filter_1(sK4,sK5)
    & r1_filter_1(sK3,sK4)
    & l3_lattices(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5)
    & l3_lattices(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4)
    & l3_lattices(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f2732,f2789,f2788,f2787])).

fof(f2787,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_filter_1(X0,X2)
                & r1_filter_1(X1,X2)
                & r1_filter_1(X0,X1)
                & l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(sK3,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(sK3,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2788,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_filter_1(sK3,X2)
            & r1_filter_1(X1,X2)
            & r1_filter_1(sK3,X1)
            & l3_lattices(X2)
            & v10_lattices(X2)
            & ~ v2_struct_0(X2) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_filter_1(sK3,X2)
          & r1_filter_1(sK4,X2)
          & r1_filter_1(sK3,sK4)
          & l3_lattices(X2)
          & v10_lattices(X2)
          & ~ v2_struct_0(X2) )
      & l3_lattices(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f2789,plain,
    ( ? [X2] :
        ( ~ r1_filter_1(sK3,X2)
        & r1_filter_1(sK4,X2)
        & r1_filter_1(sK3,sK4)
        & l3_lattices(X2)
        & v10_lattices(X2)
        & ~ v2_struct_0(X2) )
   => ( ~ r1_filter_1(sK3,sK5)
      & r1_filter_1(sK4,sK5)
      & r1_filter_1(sK3,sK4)
      & l3_lattices(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f2732,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2731])).

fof(f2731,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2711])).

fof(f2711,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l3_lattices(X2)
                  & v10_lattices(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_filter_1(X1,X2)
                    & r1_filter_1(X0,X1) )
                 => r1_filter_1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f2710])).

fof(f2710,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_filter_1(X1,X2)
                  & r1_filter_1(X0,X1) )
               => r1_filter_1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_filter_1)).

fof(f2851,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2850,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2849,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2845,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2844,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2843,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2977,plain,(
    r4_wellord1(k8_filter_1(sK3),k8_filter_1(sK5)) ),
    inference(unit_resulting_resolution,[],[f2938,f2943,f2948,f2950,f2952,f2888])).

fof(f2888,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2755])).

fof(f2755,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2754])).

fof(f2754,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1194])).

fof(f1194,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

fof(f2952,plain,(
    r4_wellord1(k8_filter_1(sK4),k8_filter_1(sK5)) ),
    inference(unit_resulting_resolution,[],[f2846,f2847,f2848,f2849,f2850,f2851,f2853,f2857])).

fof(f2857,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | ~ r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f2853,plain,(
    r1_filter_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2848,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2847,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2846,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2950,plain,(
    r4_wellord1(k8_filter_1(sK3),k8_filter_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f2843,f2844,f2845,f2846,f2847,f2848,f2852,f2857])).

fof(f2852,plain,(
    r1_filter_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f2790])).

fof(f2948,plain,(
    v1_relat_1(k8_filter_1(sK5)) ),
    inference(unit_resulting_resolution,[],[f2849,f2850,f2851,f2929])).

fof(f2929,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2781])).

fof(f2781,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2780])).

fof(f2780,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2621])).

fof(f2621,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v1_relat_1(k8_filter_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).

fof(f2943,plain,(
    v1_relat_1(k8_filter_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f2846,f2847,f2848,f2929])).

fof(f2938,plain,(
    v1_relat_1(k8_filter_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f2843,f2844,f2845,f2929])).
%------------------------------------------------------------------------------
