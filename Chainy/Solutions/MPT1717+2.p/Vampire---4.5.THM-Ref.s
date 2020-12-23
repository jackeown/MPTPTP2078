%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1717+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 144 expanded)
%              Number of leaves         :    8 (  45 expanded)
%              Depth                    :   23
%              Number of atoms          :  284 ( 876 expanded)
%              Number of equality atoms :   36 ( 148 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8676,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8675,f6265])).

fof(f6265,plain,(
    ~ v2_struct_0(sK279) ),
    inference(cnf_transformation,[],[f4999])).

fof(f4999,plain,
    ( g1_pre_topc(u1_struct_0(sK280),u1_pre_topc(sK280)) != k2_tsep_1(sK279,sK280,sK280)
    & m1_pre_topc(sK280,sK279)
    & ~ v2_struct_0(sK280)
    & l1_pre_topc(sK279)
    & v2_pre_topc(sK279)
    & ~ v2_struct_0(sK279) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK279,sK280])],[f3395,f4998,f4997])).

fof(f4997,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK279,X1,X1)
          & m1_pre_topc(X1,sK279)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK279)
      & v2_pre_topc(sK279)
      & ~ v2_struct_0(sK279) ) ),
    introduced(choice_axiom,[])).

fof(f4998,plain,
    ( ? [X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK279,X1,X1)
        & m1_pre_topc(X1,sK279)
        & ~ v2_struct_0(X1) )
   => ( g1_pre_topc(u1_struct_0(sK280),u1_pre_topc(sK280)) != k2_tsep_1(sK279,sK280,sK280)
      & m1_pre_topc(sK280,sK279)
      & ~ v2_struct_0(sK280) ) ),
    introduced(choice_axiom,[])).

fof(f3395,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3394])).

fof(f3394,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3363])).

fof(f3363,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f3362])).

fof(f3362,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

fof(f8675,plain,(
    v2_struct_0(sK279) ),
    inference(subsumption_resolution,[],[f8674,f6266])).

fof(f6266,plain,(
    v2_pre_topc(sK279) ),
    inference(cnf_transformation,[],[f4999])).

fof(f8674,plain,
    ( ~ v2_pre_topc(sK279)
    | v2_struct_0(sK279) ),
    inference(subsumption_resolution,[],[f8670,f6267])).

fof(f6267,plain,(
    l1_pre_topc(sK279) ),
    inference(cnf_transformation,[],[f4999])).

fof(f8670,plain,
    ( ~ l1_pre_topc(sK279)
    | ~ v2_pre_topc(sK279)
    | v2_struct_0(sK279) ),
    inference(resolution,[],[f8669,f6269])).

fof(f6269,plain,(
    m1_pre_topc(sK280,sK279) ),
    inference(cnf_transformation,[],[f4999])).

fof(f8669,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK280,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f8668,f8638])).

fof(f8638,plain,(
    l1_pre_topc(sK280) ),
    inference(subsumption_resolution,[],[f8635,f6267])).

fof(f8635,plain,
    ( l1_pre_topc(sK280)
    | ~ l1_pre_topc(sK279) ),
    inference(resolution,[],[f6269,f6452])).

fof(f6452,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3472])).

fof(f3472,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f8668,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK280,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK280) ) ),
    inference(resolution,[],[f8661,f6453])).

fof(f6453,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3473])).

fof(f3473,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3364])).

fof(f3364,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f8661,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK280,sK280)
      | ~ m1_pre_topc(sK280,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f8660,f6268])).

fof(f6268,plain,(
    ~ v2_struct_0(sK280) ),
    inference(cnf_transformation,[],[f4999])).

fof(f8660,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK280,sK280)
      | ~ m1_pre_topc(sK280,X0)
      | v2_struct_0(sK280)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f8657])).

fof(f8657,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK280,sK280)
      | ~ m1_pre_topc(sK280,sK280)
      | ~ m1_pre_topc(sK280,X0)
      | v2_struct_0(sK280)
      | ~ m1_pre_topc(sK280,X0)
      | v2_struct_0(sK280)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f8656,f6496])).

fof(f6496,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3497])).

fof(f3497,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3496])).

fof(f3496,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3356])).

fof(f3356,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f8656,plain,
    ( r1_tsep_1(sK280,sK280)
    | ~ m1_pre_topc(sK280,sK280) ),
    inference(subsumption_resolution,[],[f8655,f6265])).

fof(f8655,plain,
    ( ~ m1_pre_topc(sK280,sK280)
    | r1_tsep_1(sK280,sK280)
    | v2_struct_0(sK279) ),
    inference(subsumption_resolution,[],[f8654,f6266])).

fof(f8654,plain,
    ( ~ m1_pre_topc(sK280,sK280)
    | r1_tsep_1(sK280,sK280)
    | ~ v2_pre_topc(sK279)
    | v2_struct_0(sK279) ),
    inference(subsumption_resolution,[],[f8653,f6267])).

fof(f8653,plain,
    ( ~ m1_pre_topc(sK280,sK280)
    | r1_tsep_1(sK280,sK280)
    | ~ l1_pre_topc(sK279)
    | ~ v2_pre_topc(sK279)
    | v2_struct_0(sK279) ),
    inference(subsumption_resolution,[],[f8652,f6268])).

fof(f8652,plain,
    ( ~ m1_pre_topc(sK280,sK280)
    | r1_tsep_1(sK280,sK280)
    | v2_struct_0(sK280)
    | ~ l1_pre_topc(sK279)
    | ~ v2_pre_topc(sK279)
    | v2_struct_0(sK279) ),
    inference(subsumption_resolution,[],[f8651,f6269])).

fof(f8651,plain,
    ( ~ m1_pre_topc(sK280,sK280)
    | r1_tsep_1(sK280,sK280)
    | ~ m1_pre_topc(sK280,sK279)
    | v2_struct_0(sK280)
    | ~ l1_pre_topc(sK279)
    | ~ v2_pre_topc(sK279)
    | v2_struct_0(sK279) ),
    inference(duplicate_literal_removal,[],[f8650])).

fof(f8650,plain,
    ( ~ m1_pre_topc(sK280,sK280)
    | r1_tsep_1(sK280,sK280)
    | ~ m1_pre_topc(sK280,sK279)
    | v2_struct_0(sK280)
    | ~ m1_pre_topc(sK280,sK279)
    | v2_struct_0(sK280)
    | ~ l1_pre_topc(sK279)
    | ~ v2_pre_topc(sK279)
    | v2_struct_0(sK279) ),
    inference(resolution,[],[f8647,f6285])).

fof(f6285,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X2,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4567])).

fof(f4567,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X1,X2,X0)
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f3401,f4566])).

fof(f4566,plain,(
    ! [X1,X2,X0] :
      ( ( ( m1_pre_topc(X2,X1)
          | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X2,X1) )
        & ( m1_pre_topc(X1,X2)
          | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X1,X2) ) )
      | ~ sP3(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f3401,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3400])).

fof(f3400,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3365])).

fof(f3365,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2) )
                  & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).

fof(f8647,plain,
    ( ~ sP3(sK280,sK280,sK279)
    | ~ m1_pre_topc(sK280,sK280) ),
    inference(equality_resolution,[],[f8642])).

fof(f8642,plain,(
    ! [X0,X1] :
      ( k2_tsep_1(sK279,sK280,sK280) != k2_tsep_1(X0,sK280,X1)
      | ~ m1_pre_topc(sK280,X1)
      | ~ sP3(sK280,X1,X0) ) ),
    inference(superposition,[],[f6270,f6281])).

fof(f6281,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f5011])).

fof(f5011,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_pre_topc(X1,X0)
          | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X2,X0,X1) )
        & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X2,X0,X1)
          | ~ m1_pre_topc(X1,X0) )
        & ( m1_pre_topc(X0,X1)
          | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k2_tsep_1(X2,X0,X1) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1)
          | ~ m1_pre_topc(X0,X1) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f5010])).

fof(f5010,plain,(
    ! [X1,X2,X0] :
      ( ( ( m1_pre_topc(X2,X1)
          | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X2,X1) )
        & ( m1_pre_topc(X1,X2)
          | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X1,X2) ) )
      | ~ sP3(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f4566])).

fof(f6270,plain,(
    g1_pre_topc(u1_struct_0(sK280),u1_pre_topc(sK280)) != k2_tsep_1(sK279,sK280,sK280) ),
    inference(cnf_transformation,[],[f4999])).
%------------------------------------------------------------------------------
