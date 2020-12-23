%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1642+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 321 expanded)
%              Number of leaves         :   10 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  236 (1973 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3869,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3867,f3562])).

fof(f3562,plain,(
    ~ r1_orders_2(sK0,sK1,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f3561,f3320])).

fof(f3320,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3277,plain,
    ( ~ r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3226,f3276,f3275,f3274])).

fof(f3274,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k6_waybel_0(X0,X2),k6_waybel_0(X0,X1))
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_waybel_0(sK0,X2),k6_waybel_0(sK0,X1))
              & r1_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3275,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k6_waybel_0(sK0,X2),k6_waybel_0(sK0,X1))
            & r1_orders_2(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k6_waybel_0(sK0,X2),k6_waybel_0(sK0,sK1))
          & r1_orders_2(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3276,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k6_waybel_0(sK0,X2),k6_waybel_0(sK0,sK1))
        & r1_orders_2(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))
      & r1_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3226,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_waybel_0(X0,X2),k6_waybel_0(X0,X1))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3225])).

fof(f3225,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_waybel_0(X0,X2),k6_waybel_0(X0,X1))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3204])).

fof(f3204,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                 => r1_tarski(k6_waybel_0(X0,X2),k6_waybel_0(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3203])).

fof(f3203,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => r1_tarski(k6_waybel_0(X0,X2),k6_waybel_0(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_0)).

fof(f3561,plain,
    ( ~ r1_orders_2(sK0,sK1,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3560,f3322])).

fof(f3322,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3560,plain,
    ( ~ r1_orders_2(sK0,sK1,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3559,f3323])).

fof(f3323,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3559,plain,
    ( ~ r1_orders_2(sK0,sK1,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3558,f3524])).

fof(f3524,plain,(
    m1_subset_1(sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3424,f3432,f3365])).

fof(f3365,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3257])).

fof(f3257,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3256])).

fof(f3256,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f3432,plain,(
    r2_hidden(sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)),k6_waybel_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f3326,f3341])).

fof(f3341,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3286])).

fof(f3286,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3284,f3285])).

fof(f3285,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3284,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3283])).

fof(f3283,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3237])).

fof(f3237,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f3326,plain,(
    ~ r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3424,plain,(
    m1_subset_1(k6_waybel_0(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3320,f3322,f3324,f3352])).

fof(f3352,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3244])).

fof(f3244,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3243])).

fof(f3243,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3171])).

fof(f3171,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_waybel_0)).

fof(f3324,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3558,plain,
    ( ~ r1_orders_2(sK0,sK1,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | ~ m1_subset_1(sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3433,f3354])).

fof(f3354,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3293])).

fof(f3293,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3246])).

fof(f3246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3245])).

fof(f3245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3198])).

fof(f3198,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f3433,plain,(
    ~ r2_hidden(sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)),k6_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f3326,f3342])).

fof(f3342,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3286])).

fof(f3867,plain,(
    r1_orders_2(sK0,sK1,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f3321,f3322,f3323,f3325,f3324,f3524,f3539,f3356])).

fof(f3356,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3250])).

fof(f3250,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f3249])).

fof(f3249,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1954])).

fof(f1954,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f3539,plain,(
    r1_orders_2(sK0,sK2,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f3538,f3320])).

fof(f3538,plain,
    ( r1_orders_2(sK0,sK2,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3537,f3322])).

fof(f3537,plain,
    ( r1_orders_2(sK0,sK2,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3536,f3324])).

fof(f3536,plain,
    ( r1_orders_2(sK0,sK2,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3532,f3524])).

fof(f3532,plain,
    ( r1_orders_2(sK0,sK2,sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)))
    | ~ m1_subset_1(sK4(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3432,f3353])).

fof(f3353,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_waybel_0(X0,X1))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3293])).

fof(f3325,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3321,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3277])).
%------------------------------------------------------------------------------
