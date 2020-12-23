%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2062+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 196 expanded)
%              Number of leaves         :    7 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  221 (1212 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6286,f5138])).

fof(f5138,plain,(
    ~ r2_hidden(sK12(sK8,sK10,sK11),sK10) ),
    inference(subsumption_resolution,[],[f5137,f4803])).

fof(f4803,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f4691])).

fof(f4691,plain,
    ( ~ r2_waybel_7(sK8,sK10,sK11)
    & r2_waybel_7(sK8,sK9,sK11)
    & r1_tarski(sK9,sK10)
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f4573,f4690,f4689])).

fof(f4689,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r2_waybel_7(X0,X2,X3)
            & r2_waybel_7(X0,X1,X3)
            & r1_tarski(X1,X2) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r2_waybel_7(sK8,X2,X3)
          & r2_waybel_7(sK8,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f4690,plain,
    ( ? [X3,X2,X1] :
        ( ~ r2_waybel_7(sK8,X2,X3)
        & r2_waybel_7(sK8,X1,X3)
        & r1_tarski(X1,X2) )
   => ( ~ r2_waybel_7(sK8,sK10,sK11)
      & r2_waybel_7(sK8,sK9,sK11)
      & r1_tarski(sK9,sK10) ) ),
    introduced(choice_axiom,[])).

fof(f4573,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4572])).

fof(f4572,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4529])).

fof(f4529,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2,X3] :
            ( ( r2_waybel_7(X0,X1,X3)
              & r1_tarski(X1,X2) )
           => r2_waybel_7(X0,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f4528])).

fof(f4528,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2,X3] :
          ( ( r2_waybel_7(X0,X1,X3)
            & r1_tarski(X1,X2) )
         => r2_waybel_7(X0,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow19)).

fof(f5137,plain,
    ( ~ r2_hidden(sK12(sK8,sK10,sK11),sK10)
    | ~ v2_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f5127,f4804])).

fof(f4804,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f4691])).

fof(f5127,plain,
    ( ~ r2_hidden(sK12(sK8,sK10,sK11),sK10)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(resolution,[],[f4807,f4812])).

fof(f4812,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK12(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4695])).

fof(f4695,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(X2,sK12(X0,X1,X2))
              & v3_pre_topc(sK12(X0,X1,X2),X0)
              & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f4693,f4694])).

fof(f4694,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK12(X0,X1,X2),X1)
        & r2_hidden(X2,sK12(X0,X1,X2))
        & v3_pre_topc(sK12(X0,X1,X2),X0)
        & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4693,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f4692])).

fof(f4692,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f4575])).

fof(f4575,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f4574])).

fof(f4574,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4139])).

fof(f4139,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f4807,plain,(
    ~ r2_waybel_7(sK8,sK10,sK11) ),
    inference(cnf_transformation,[],[f4691])).

fof(f6286,plain,(
    r2_hidden(sK12(sK8,sK10,sK11),sK10) ),
    inference(resolution,[],[f5845,f5079])).

fof(f5079,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,sK9)
      | r2_hidden(X14,sK10) ) ),
    inference(resolution,[],[f4805,f4840])).

fof(f4840,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4711])).

fof(f4711,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK16(X0,X1),X1)
          & r2_hidden(sK16(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f4709,f4710])).

fof(f4710,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK16(X0,X1),X1)
        & r2_hidden(sK16(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4709,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f4708])).

fof(f4708,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4590])).

fof(f4590,plain,(
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

fof(f4805,plain,(
    r1_tarski(sK9,sK10) ),
    inference(cnf_transformation,[],[f4691])).

fof(f5845,plain,(
    r2_hidden(sK12(sK8,sK10,sK11),sK9) ),
    inference(subsumption_resolution,[],[f5844,f5134])).

fof(f5134,plain,(
    v3_pre_topc(sK12(sK8,sK10,sK11),sK8) ),
    inference(subsumption_resolution,[],[f5133,f4803])).

fof(f5133,plain,
    ( v3_pre_topc(sK12(sK8,sK10,sK11),sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f5125,f4804])).

fof(f5125,plain,
    ( v3_pre_topc(sK12(sK8,sK10,sK11),sK8)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(resolution,[],[f4807,f4810])).

fof(f4810,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK12(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4695])).

fof(f5844,plain,
    ( ~ v3_pre_topc(sK12(sK8,sK10,sK11),sK8)
    | r2_hidden(sK12(sK8,sK10,sK11),sK9) ),
    inference(subsumption_resolution,[],[f5816,f5136])).

fof(f5136,plain,(
    r2_hidden(sK11,sK12(sK8,sK10,sK11)) ),
    inference(subsumption_resolution,[],[f5135,f4803])).

fof(f5135,plain,
    ( r2_hidden(sK11,sK12(sK8,sK10,sK11))
    | ~ v2_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f5126,f4804])).

fof(f5126,plain,
    ( r2_hidden(sK11,sK12(sK8,sK10,sK11))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(resolution,[],[f4807,f4811])).

fof(f4811,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK12(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4695])).

fof(f5816,plain,
    ( ~ r2_hidden(sK11,sK12(sK8,sK10,sK11))
    | ~ v3_pre_topc(sK12(sK8,sK10,sK11),sK8)
    | r2_hidden(sK12(sK8,sK10,sK11),sK9) ),
    inference(resolution,[],[f5122,f5132])).

fof(f5132,plain,(
    m1_subset_1(sK12(sK8,sK10,sK11),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(subsumption_resolution,[],[f5131,f4803])).

fof(f5131,plain,
    ( m1_subset_1(sK12(sK8,sK10,sK11),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v2_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f5124,f4804])).

fof(f5124,plain,
    ( m1_subset_1(sK12(sK8,sK10,sK11),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(resolution,[],[f4807,f4809])).

fof(f4809,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4695])).

fof(f5122,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
      | ~ r2_hidden(sK11,X1)
      | ~ v3_pre_topc(X1,sK8)
      | r2_hidden(X1,sK9) ) ),
    inference(subsumption_resolution,[],[f5121,f4803])).

fof(f5121,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK9)
      | ~ r2_hidden(sK11,X1)
      | ~ v3_pre_topc(X1,sK8)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
      | ~ v2_pre_topc(sK8) ) ),
    inference(subsumption_resolution,[],[f5117,f4804])).

fof(f5117,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK9)
      | ~ r2_hidden(sK11,X1)
      | ~ v3_pre_topc(X1,sK8)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
      | ~ l1_pre_topc(sK8)
      | ~ v2_pre_topc(sK8) ) ),
    inference(resolution,[],[f4806,f4808])).

fof(f4808,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4695])).

fof(f4806,plain,(
    r2_waybel_7(sK8,sK9,sK11) ),
    inference(cnf_transformation,[],[f4691])).
%------------------------------------------------------------------------------
