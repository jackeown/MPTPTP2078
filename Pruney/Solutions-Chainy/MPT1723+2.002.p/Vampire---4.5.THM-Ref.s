%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 795 expanded)
%              Number of leaves         :    8 ( 345 expanded)
%              Depth                    :   54
%              Number of atoms          :  664 (11016 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(subsumption_resolution,[],[f401,f17])).

fof(f17,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
        & m1_pre_topc(sK2,sK3) )
      | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
        & m1_pre_topc(sK1,sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                        & m1_pre_topc(X2,X3) )
                      | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                        & m1_pre_topc(X1,X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3))
                    & m1_pre_topc(X2,X3) )
                  | ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2))
                    & m1_pre_topc(X1,X3) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,sK1,X3))
                  & m1_pre_topc(X2,X3) )
                | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X2))
                  & m1_pre_topc(sK1,X3) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,sK1,X3))
                & m1_pre_topc(X2,X3) )
              | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X2))
                & m1_pre_topc(sK1,X3) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,X3))
              & m1_pre_topc(sK2,X3) )
            | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,sK2))
              & m1_pre_topc(sK1,X3) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,X3))
            & m1_pre_topc(sK2,X3) )
          | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,sK2))
            & m1_pre_topc(sK1,X3) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
          & m1_pre_topc(sK2,sK3) )
        | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
          & m1_pre_topc(sK1,sK3) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                        & ( m1_pre_topc(X1,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f401,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f400,f18])).

fof(f18,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f400,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f399,f19])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f399,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f398,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f398,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f397,f23])).

fof(f23,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f397,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f396,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f396,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f395,f21])).

fof(f21,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f395,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f394,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f394,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f393,f25])).

fof(f25,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f393,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f392,f93])).

fof(f93,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f70,f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f63,f19])).

fof(f63,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f21,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f392,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f391,f271])).

fof(f271,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f270,f27])).

fof(f27,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f270,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f269,f17])).

fof(f269,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f268,f18])).

fof(f268,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f267,f19])).

fof(f267,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f266,f20])).

fof(f266,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f265,f21])).

fof(f265,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f264,f24])).

fof(f264,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f263,f25])).

fof(f263,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f262,f22])).

fof(f262,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f261,f23])).

fof(f261,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f153])).

fof(f153,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f102,f31])).

fof(f102,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f95,f19])).

fof(f95,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f23,f32])).

fof(f260,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f259,f26])).

fof(f26,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f259,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X4)
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f28,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f391,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f390,f26])).

fof(f390,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f375,f33])).

fof(f375,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f374,f17])).

fof(f374,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f373,f18])).

fof(f373,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f372,f19])).

fof(f372,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f371,f20])).

fof(f371,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f370,f21])).

fof(f370,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f369,f24])).

fof(f369,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f368,f25])).

fof(f368,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f367,f22])).

fof(f367,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f366,f23])).

fof(f366,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f365,f334])).

fof(f334,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f333,f17])).

fof(f333,plain,
    ( m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f332,f18])).

fof(f332,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f331,f19])).

fof(f331,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f330,f22])).

fof(f330,plain,
    ( m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f329,f23])).

fof(f329,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f328,f20])).

fof(f328,plain,
    ( m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f327,f21])).

fof(f327,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f326,f24])).

fof(f326,plain,
    ( m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f325,f25])).

fof(f325,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f324,f93])).

fof(f324,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f323,f271])).

fof(f323,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f322,f26])).

fof(f322,plain,
    ( m1_pre_topc(sK1,sK3)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( m1_pre_topc(sK1,sK3)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f29,f33])).

fof(f29,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f365,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f364,f153])).

fof(f364,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f363,f26])).

fof(f363,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f30,f33])).

fof(f30,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (26947)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.46  % (26965)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (26958)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.46  % (26961)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.46  % (26961)Refutation not found, incomplete strategy% (26961)------------------------------
% 0.21/0.46  % (26961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (26953)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.46  % (26961)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (26961)Memory used [KB]: 5373
% 0.21/0.46  % (26961)Time elapsed: 0.006 s
% 0.21/0.46  % (26961)------------------------------
% 0.21/0.46  % (26961)------------------------------
% 0.21/0.46  % (26954)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (26958)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (26948)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.48  % (26963)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f401,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    (((((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) & m1_pre_topc(sK2,sK3)) | (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,sK1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X2)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,sK1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X2)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,X3)) & m1_pre_topc(sK2,X3)) | (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,sK2)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X3] : (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,X3)) & m1_pre_topc(sK2,X3)) | (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,sK2)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) & m1_pre_topc(sK2,sK3)) | (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f400,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f400,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f399,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f398,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f398,plain,(
% 0.21/0.48    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f397,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f397,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f396,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f395,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f395,plain,(
% 0.21/0.48    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f394,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ~v2_struct_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f394,plain,(
% 0.21/0.48    v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f393,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f393,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f392,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK1)),
% 0.21/0.48    inference(resolution,[],[f70,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f19])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f21,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f392,plain,(
% 0.21/0.48    ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f391,f271])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f270,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f269,f17])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f268,f18])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f267,f19])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f266,f20])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f265,f21])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f264,f24])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f263,f25])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f262,f22])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f261,f23])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f260,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK2)),
% 0.21/0.48    inference(resolution,[],[f102,f31])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    l1_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f19])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f23,f32])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f259,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~r1_tsep_1(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f258])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f28,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | m1_pre_topc(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f391,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f390,f26])).
% 0.21/0.48  fof(f390,plain,(
% 0.21/0.48    r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f389])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f375,f33])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f374,f17])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f373,f18])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f372,f19])).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f371,f20])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f370,f21])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f369,f24])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f368,f25])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f367,f22])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f366,f23])).
% 0.21/0.48  fof(f366,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f365,f334])).
% 0.21/0.48  fof(f334,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f333,f17])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f332,f18])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f331,f19])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f330,f22])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f329,f23])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f328,f20])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f327,f21])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f326,f24])).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f325,f25])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f324,f93])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f323,f271])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f322,f26])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f321])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK3) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f29,f33])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | m1_pre_topc(sK1,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f364,f153])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f363,f26])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f362])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f30,f33])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (26958)------------------------------
% 0.21/0.48  % (26958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26958)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (26958)Memory used [KB]: 5628
% 0.21/0.48  % (26958)Time elapsed: 0.067 s
% 0.21/0.48  % (26958)------------------------------
% 0.21/0.48  % (26958)------------------------------
% 0.21/0.48  % (26946)Success in time 0.13 s
%------------------------------------------------------------------------------
