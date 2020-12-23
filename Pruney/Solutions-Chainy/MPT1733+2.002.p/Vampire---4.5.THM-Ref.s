%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 972 expanded)
%              Number of leaves         :    6 ( 438 expanded)
%              Depth                    :   21
%              Number of atoms          :  534 (16383 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(global_subsumption,[],[f25,f26,f167,f208,f288])).

fof(f288,plain,(
    r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f16,f18,f17,f22,f21,f19,f270,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | r1_tsep_1(X1,X2)
      | r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X0,X2) ) ),
    inference(subsumption_resolution,[],[f52,f13])).

fof(f13,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
        & ( r1_tsep_1(sK3,sK2)
          | r1_tsep_1(sK3,sK1) ) )
      | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
        & ( r1_tsep_1(sK2,sK3)
          | r1_tsep_1(sK1,sK3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f11,f10,f9,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                        & ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) ) )
                      | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                        & ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) ) ) )
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
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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

fof(f9,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) ) )
                  | ( ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3)
                    & ( r1_tsep_1(X2,X3)
                      | r1_tsep_1(X1,X3) ) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK1) ) )
                | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3)
                  & ( r1_tsep_1(X2,X3)
                    | r1_tsep_1(sK1,X3) ) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK1) ) )
              | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3)
                & ( r1_tsep_1(X2,X3)
                  | r1_tsep_1(sK1,X3) ) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))
              & ( r1_tsep_1(X3,sK2)
                | r1_tsep_1(X3,sK1) ) )
            | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
              & ( r1_tsep_1(sK2,X3)
                | r1_tsep_1(sK1,X3) ) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X3] :
        ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))
            & ( r1_tsep_1(X3,sK2)
              | r1_tsep_1(X3,sK1) ) )
          | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
            & ( r1_tsep_1(sK2,X3)
              | r1_tsep_1(sK1,X3) ) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
          & ( r1_tsep_1(sK3,sK2)
            | r1_tsep_1(sK3,sK1) ) )
        | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
          & ( r1_tsep_1(sK2,sK3)
            | r1_tsep_1(sK1,sK3) ) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
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
                     => ( ( ( r1_tsep_1(X3,X2)
                            | r1_tsep_1(X3,X1) )
                         => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                        & ( ( r1_tsep_1(X2,X3)
                            | r1_tsep_1(X1,X3) )
                         => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      & ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f51,f14])).

fof(f14,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X0,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f30,f15])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X3,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X3,X1) )
                      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    & ( ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X1,X3) )
                      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X3,X1) )
                      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    & ( ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X1,X3) )
                      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

fof(f270,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(global_subsumption,[],[f212,f266])).

fof(f266,plain,(
    ~ r1_tsep_1(sK3,sK1) ),
    inference(global_subsumption,[],[f25,f26,f167,f208,f265])).

fof(f265,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f264,f16])).

fof(f264,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f261,f22])).

fof(f261,plain,
    ( r1_tsep_1(sK1,sK2)
    | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f133,f17])).

fof(f133,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X1,sK2)
      | r1_tsep_1(sK3,k2_tsep_1(sK0,X1,sK2))
      | v2_struct_0(X1)
      | ~ r1_tsep_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f130,f18])).

fof(f130,plain,(
    ! [X1] :
      ( r1_tsep_1(sK3,k2_tsep_1(sK0,X1,sK2))
      | r1_tsep_1(X1,sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(sK3,X1) ) ),
    inference(resolution,[],[f72,f19])).

fof(f72,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,sK0)
      | r1_tsep_1(sK3,k2_tsep_1(sK0,X4,X5))
      | r1_tsep_1(X4,X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ r1_tsep_1(sK3,X4) ) ),
    inference(subsumption_resolution,[],[f69,f20])).

fof(f69,plain,(
    ! [X4,X5] :
      ( r1_tsep_1(X4,X5)
      | r1_tsep_1(sK3,k2_tsep_1(sK0,X4,X5))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ r1_tsep_1(sK3,X4) ) ),
    inference(resolution,[],[f45,f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | r1_tsep_1(X1,X2)
      | r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f44,f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f43,f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f29,f15])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X3,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f212,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f211,f24])).

fof(f24,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f211,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f210,f167])).

fof(f210,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f208,f23])).

fof(f23,plain,
    ( r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f22,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f208,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f207,f16])).

fof(f207,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | v2_struct_0(sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f204,f22])).

fof(f204,plain,
    ( r1_tsep_1(sK1,sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | v2_struct_0(sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f110,f17])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X1,sK2)
      | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f107,f18])).

fof(f107,plain,(
    ! [X1] :
      ( r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3)
      | r1_tsep_1(X1,sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(sK2,sK3) ) ),
    inference(resolution,[],[f66,f19])).

fof(f66,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,sK0)
      | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3)
      | r1_tsep_1(X4,X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ r1_tsep_1(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f63,plain,(
    ! [X4,X5] :
      ( r1_tsep_1(X4,X5)
      | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ r1_tsep_1(X5,sK3) ) ),
    inference(resolution,[],[f36,f21])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,sK0)
      | r1_tsep_1(X0,X1)
      | r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(subsumption_resolution,[],[f35,f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2)
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f34,f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2)
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f28,f15])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X2,X3)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f167,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f166,f16])).

fof(f166,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | v2_struct_0(sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f163,f22])).

fof(f163,plain,
    ( r1_tsep_1(sK1,sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | v2_struct_0(sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f94,f17])).

fof(f94,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X1,sK2)
      | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f91,f18])).

fof(f91,plain,(
    ! [X1] :
      ( r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3)
      | r1_tsep_1(X1,sK2)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X1,sK3) ) ),
    inference(resolution,[],[f42,f19])).

fof(f42,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,sK0)
      | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3)
      | r1_tsep_1(X4,X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ r1_tsep_1(X4,sK3) ) ),
    inference(subsumption_resolution,[],[f39,f20])).

fof(f39,plain,(
    ! [X4,X5] :
      ( r1_tsep_1(X4,X5)
      | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ r1_tsep_1(X4,sK3) ) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,sK0)
      | r1_tsep_1(X0,X1)
      | r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X0,X2) ) ),
    inference(subsumption_resolution,[],[f32,f13])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2)
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f31,f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2)
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X0,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f27,f15])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X1,X3)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (16107)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.43  % (16107)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f289,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f25,f26,f167,f208,f288])).
% 0.21/0.43  fof(f288,plain,(
% 0.21/0.43    r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f20,f16,f18,f17,f22,f21,f19,f270,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK0) | r1_tsep_1(X1,X2) | r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2)) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(X0,X2)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f52,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    (((((~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) & (r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f11,f10,f9,f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) & (r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) & (r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (((~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) & (r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f4])).
% 0.21/0.43  fof(f4,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => (((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) & ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f2])).
% 0.21/0.43  fof(f2,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => (((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) & ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(X0,X2) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f51,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    v2_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(X0,X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f30,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~r1_tsep_1(X3,X2) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1)) | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) & ((~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)) | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1)) | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) & ((~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)) | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).
% 0.21/0.43  fof(f270,plain,(
% 0.21/0.43    r1_tsep_1(sK3,sK2)),
% 0.21/0.43    inference(global_subsumption,[],[f212,f266])).
% 0.21/0.43  fof(f266,plain,(
% 0.21/0.43    ~r1_tsep_1(sK3,sK1)),
% 0.21/0.43    inference(global_subsumption,[],[f25,f26,f167,f208,f265])).
% 0.21/0.43  fof(f265,plain,(
% 0.21/0.43    r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | ~r1_tsep_1(sK3,sK1)),
% 0.21/0.43    inference(subsumption_resolution,[],[f264,f16])).
% 0.21/0.43  fof(f264,plain,(
% 0.21/0.43    r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~r1_tsep_1(sK3,sK1)),
% 0.21/0.43    inference(subsumption_resolution,[],[f261,f22])).
% 0.21/0.43  fof(f261,plain,(
% 0.21/0.43    r1_tsep_1(sK1,sK2) | r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~r1_tsep_1(sK3,sK1)),
% 0.21/0.43    inference(resolution,[],[f133,f17])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    ( ! [X1] : (~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,sK2) | r1_tsep_1(sK3,k2_tsep_1(sK0,X1,sK2)) | v2_struct_0(X1) | ~r1_tsep_1(sK3,X1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f130,f18])).
% 0.21/0.43  fof(f130,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tsep_1(sK3,k2_tsep_1(sK0,X1,sK2)) | r1_tsep_1(X1,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(sK3,X1)) )),
% 0.21/0.43    inference(resolution,[],[f72,f19])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X4,X5] : (~m1_pre_topc(X5,sK0) | r1_tsep_1(sK3,k2_tsep_1(sK0,X4,X5)) | r1_tsep_1(X4,X5) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~r1_tsep_1(sK3,X4)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f69,f20])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X4,X5] : (r1_tsep_1(X4,X5) | r1_tsep_1(sK3,k2_tsep_1(sK0,X4,X5)) | v2_struct_0(sK3) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~r1_tsep_1(sK3,X4)) )),
% 0.21/0.43    inference(resolution,[],[f45,f21])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK0) | r1_tsep_1(X1,X2) | r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2)) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(X0,X1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f44,f13])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(X0,X1) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f43,f14])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tsep_1(X0,k2_tsep_1(sK0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(X0,X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f29,f15])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~r1_tsep_1(X3,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f212,plain,(
% 0.21/0.43    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1)),
% 0.21/0.43    inference(subsumption_resolution,[],[f211,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | r1_tsep_1(sK3,sK1) | r1_tsep_1(sK3,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f211,plain,(
% 0.21/0.43    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | r1_tsep_1(sK3,sK1) | r1_tsep_1(sK3,sK2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f210,f167])).
% 0.21/0.43  fof(f210,plain,(
% 0.21/0.43    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | r1_tsep_1(sK3,sK1) | r1_tsep_1(sK3,sK2) | r1_tsep_1(sK1,sK3)),
% 0.21/0.43    inference(resolution,[],[f208,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    r1_tsep_1(sK2,sK3) | r1_tsep_1(sK3,sK1) | r1_tsep_1(sK3,sK2) | r1_tsep_1(sK1,sK3)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    m1_pre_topc(sK2,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    m1_pre_topc(sK3,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ~r1_tsep_1(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    m1_pre_topc(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ~v2_struct_0(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ~v2_struct_0(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ~v2_struct_0(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f208,plain,(
% 0.21/0.44    ~r1_tsep_1(sK2,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f207,f16])).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | v2_struct_0(sK1) | ~r1_tsep_1(sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f204,f22])).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    r1_tsep_1(sK1,sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | v2_struct_0(sK1) | ~r1_tsep_1(sK2,sK3)),
% 0.21/0.44    inference(resolution,[],[f110,f17])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X1] : (~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,sK2) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3) | v2_struct_0(X1) | ~r1_tsep_1(sK2,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f107,f18])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ( ! [X1] : (r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3) | r1_tsep_1(X1,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(sK2,sK3)) )),
% 0.21/0.44    inference(resolution,[],[f66,f19])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X4,X5] : (~m1_pre_topc(X5,sK0) | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3) | r1_tsep_1(X4,X5) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~r1_tsep_1(X5,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f63,f20])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X4,X5] : (r1_tsep_1(X4,X5) | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3) | v2_struct_0(sK3) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~r1_tsep_1(X5,sK3)) )),
% 0.21/0.44    inference(resolution,[],[f36,f21])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,sK0) | r1_tsep_1(X0,X1) | r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X1,X2)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f35,f13])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f34,f14])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X1,X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f28,f15])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~r1_tsep_1(X2,X3) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    ~r1_tsep_1(sK1,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f166,f16])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | v2_struct_0(sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f163,f22])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    r1_tsep_1(sK1,sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | v2_struct_0(sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.44    inference(resolution,[],[f94,f17])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    ( ! [X1] : (~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,sK2) | r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3) | v2_struct_0(X1) | ~r1_tsep_1(X1,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f91,f18])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ( ! [X1] : (r1_tsep_1(k2_tsep_1(sK0,X1,sK2),sK3) | r1_tsep_1(X1,sK2) | v2_struct_0(sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~r1_tsep_1(X1,sK3)) )),
% 0.21/0.44    inference(resolution,[],[f42,f19])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X4,X5] : (~m1_pre_topc(X5,sK0) | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3) | r1_tsep_1(X4,X5) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~r1_tsep_1(X4,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f39,f20])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X4,X5] : (r1_tsep_1(X4,X5) | r1_tsep_1(k2_tsep_1(sK0,X4,X5),sK3) | v2_struct_0(sK3) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | ~r1_tsep_1(X4,sK3)) )),
% 0.21/0.44    inference(resolution,[],[f33,f21])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,sK0) | r1_tsep_1(X0,X1) | r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X0,X2)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f32,f13])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X0,X2) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f31,f14])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tsep_1(k2_tsep_1(sK0,X0,X1),X2) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~r1_tsep_1(X0,X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f27,f15])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~r1_tsep_1(X1,X3) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (16107)------------------------------
% 0.21/0.44  % (16107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (16107)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (16107)Memory used [KB]: 5756
% 0.21/0.44  % (16107)Time elapsed: 0.039 s
% 0.21/0.44  % (16107)------------------------------
% 0.21/0.44  % (16107)------------------------------
% 0.21/0.44  % (16086)Success in time 0.081 s
%------------------------------------------------------------------------------
