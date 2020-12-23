%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1725+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:17 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :  278 (17250 expanded)
%              Number of clauses        :  224 (3964 expanded)
%              Number of leaves         :   11 (6387 expanded)
%              Depth                    :   37
%              Number of atoms          : 1843 (251350 expanded)
%              Number of equality atoms :  524 (6105 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   32 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                        & ( m1_pre_topc(X1,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
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
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
              & m1_pre_topc(X2,X3) )
            | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
              & m1_pre_topc(X1,X3) ) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ( r1_tsep_1(k2_tsep_1(X0,sK3,X1),X2)
              | r1_tsep_1(k2_tsep_1(X0,X1,sK3),X2) )
            & m1_pre_topc(X2,sK3) )
          | ( ( r1_tsep_1(k2_tsep_1(X0,X2,sK3),X1)
              | r1_tsep_1(k2_tsep_1(X0,sK3,X2),X1) )
            & m1_pre_topc(X1,sK3) ) )
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                    | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                  & m1_pre_topc(X2,X3) )
                | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                    | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                  & m1_pre_topc(X1,X3) ) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),sK2)
                  | r1_tsep_1(k2_tsep_1(X0,X1,X3),sK2) )
                & m1_pre_topc(sK2,X3) )
              | ( ( r1_tsep_1(k2_tsep_1(X0,sK2,X3),X1)
                  | r1_tsep_1(k2_tsep_1(X0,X3,sK2),X1) )
                & m1_pre_topc(X1,X3) ) )
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,sK1),X2)
                      | r1_tsep_1(k2_tsep_1(X0,sK1,X3),X2) )
                    & m1_pre_topc(X2,X3) )
                  | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),sK1)
                      | r1_tsep_1(k2_tsep_1(X0,X3,X2),sK1) )
                    & m1_pre_topc(sK1,X3) ) )
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                        & m1_pre_topc(X2,X3) )
                      | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
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
                  ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1) )
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

fof(f28,plain,
    ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
          | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) )
        & m1_pre_topc(sK2,sK3) )
      | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
          | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
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
                 => ( ( ( ( ~ r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          & ~ r1_tsep_1(X2,X3) )
                        | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          & ~ r1_tsep_1(X1,X2) ) )
                     => k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) )
                    & ( ~ r1_tsep_1(X1,X2)
                     => k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3)
                      | ( ( r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          | r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          | r1_tsep_1(X1,X2) ) ) )
                    & ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
                      | r1_tsep_1(X1,X2) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3)
                      | ( ( r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          | r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          | r1_tsep_1(X1,X2) ) ) )
                    & ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
                      | r1_tsep_1(X1,X2) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
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
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
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
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1546,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1548,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_417,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X0,X1)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_418,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0)
    | k2_tsep_1(sK0,X1,X0) = k2_tsep_1(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_422,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | k2_tsep_1(sK0,X1,X0) = k2_tsep_1(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_28,c_26])).

cnf(c_423,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tsep_1(sK0,X1,X0) = k2_tsep_1(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_1077,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_tsep_1(sK0,X1,X0) = k2_tsep_1(sK0,X0,X1)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_423])).

cnf(c_1538,plain,
    ( k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0)
    | r1_tsep_1(X1,X0) = iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1078,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_423])).

cnf(c_1102,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_1103,plain,
    ( k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0)
    | r1_tsep_1(X1,X0) = iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1550,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1076,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_423])).

cnf(c_1539,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_2516,plain,
    ( v2_struct_0(sK3) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1539])).

cnf(c_4623,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1538,c_36,c_1102,c_1103,c_2516])).

cnf(c_4624,plain,
    ( k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0)
    | r1_tsep_1(X1,X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_4623])).

cnf(c_4628,plain,
    ( k2_tsep_1(sK0,sK2,X0) = k2_tsep_1(sK0,X0,sK2)
    | r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_4624])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_34,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5038,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tsep_1(X0,sK2) = iProver_top
    | k2_tsep_1(sK0,sK2,X0) = k2_tsep_1(sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4628,c_34])).

cnf(c_5039,plain,
    ( k2_tsep_1(sK0,sK2,X0) = k2_tsep_1(sK0,X0,sK2)
    | r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5038])).

cnf(c_5046,plain,
    ( k2_tsep_1(sK0,sK2,sK1) = k2_tsep_1(sK0,sK1,sK2)
    | r1_tsep_1(sK1,sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_5039])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_32,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,plain,
    ( r1_tsep_1(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5118,plain,
    ( k2_tsep_1(sK0,sK2,sK1) = k2_tsep_1(sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5046,c_32,c_38])).

cnf(c_14,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X3,X1))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_287,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X3,X1))
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_288,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X2,X1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_292,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_28,c_26])).

cnf(c_293,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X2,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_1543,plain,
    ( r1_tsep_1(X0,X1) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X2,X1)) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_5787,plain,
    ( r1_tsep_1(sK2,sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X0,sK1)) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5118,c_1543])).

cnf(c_33,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_35,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7036,plain,
    ( r1_tsep_1(sK2,sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X0,sK1)) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5787,c_32,c_33,c_34,c_35])).

cnf(c_4627,plain,
    ( k2_tsep_1(sK0,sK3,X0) = k2_tsep_1(sK0,X0,sK3)
    | r1_tsep_1(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_4624])).

cnf(c_4646,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tsep_1(X0,sK3) = iProver_top
    | k2_tsep_1(sK0,sK3,X0) = k2_tsep_1(sK0,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4627,c_36])).

cnf(c_4647,plain,
    ( k2_tsep_1(sK0,sK3,X0) = k2_tsep_1(sK0,X0,sK3)
    | r1_tsep_1(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4646])).

cnf(c_4654,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | r1_tsep_1(sK1,sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_4647])).

cnf(c_5013,plain,
    ( r1_tsep_1(sK1,sK3) = iProver_top
    | k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4654,c_32])).

cnf(c_5014,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | r1_tsep_1(sK1,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5013])).

cnf(c_4,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_692,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_693,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_695,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_28,c_26])).

cnf(c_696,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_1529,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_5017,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | r1_tsep_1(sK1,X0) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5014,c_1529])).

cnf(c_37,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4629,plain,
    ( k2_tsep_1(sK0,sK1,X0) = k2_tsep_1(sK0,X0,sK1)
    | r1_tsep_1(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_4624])).

cnf(c_5145,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tsep_1(X0,sK1) = iProver_top
    | k2_tsep_1(sK0,sK1,X0) = k2_tsep_1(sK0,X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4629,c_32])).

cnf(c_5146,plain,
    ( k2_tsep_1(sK0,sK1,X0) = k2_tsep_1(sK0,X0,sK1)
    | r1_tsep_1(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5145])).

cnf(c_5151,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | r1_tsep_1(sK3,sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_5146])).

cnf(c_5162,plain,
    ( r1_tsep_1(sK3,sK1) = iProver_top
    | k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5151,c_36])).

cnf(c_5163,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | r1_tsep_1(sK3,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_5162])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1552,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4653,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(sK2,sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_4647])).

cnf(c_5000,plain,
    ( r1_tsep_1(sK2,sK3) = iProver_top
    | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4653,c_34])).

cnf(c_5001,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5000])).

cnf(c_3,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_492,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_493,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_497,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_28,c_26])).

cnf(c_498,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_1535,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_5005,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5001,c_1535])).

cnf(c_7077,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5005,c_34,c_35,c_36,c_37])).

cnf(c_7081,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_7077])).

cnf(c_5018,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5014,c_1535])).

cnf(c_7091,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | m1_pre_topc(sK1,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5018,c_32,c_33,c_36,c_37])).

cnf(c_7095,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    inference(superposition,[status(thm)],[c_7081,c_7091])).

cnf(c_17,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1553,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7111,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7095,c_1553])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7152,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7111,c_32,c_33,c_36,c_37,c_39,c_5018])).

cnf(c_6,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_622,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_623,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_625,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_28,c_26])).

cnf(c_626,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_625])).

cnf(c_1741,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(sK3,X0)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_3203,plain,
    ( r1_tsep_1(sK1,X0)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_8025,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3203])).

cnf(c_8026,plain,
    ( r1_tsep_1(sK1,sK2) = iProver_top
    | r1_tsep_1(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8025])).

cnf(c_9172,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5017,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_5163,c_7152,c_8026])).

cnf(c_5004,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(sK2,X0) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5001,c_1529])).

cnf(c_5044,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(sK3,sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_5039])).

cnf(c_5056,plain,
    ( r1_tsep_1(sK3,sK2) = iProver_top
    | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5044,c_36])).

cnf(c_5057,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5056])).

cnf(c_7,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_587,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_588,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_590,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_588,c_28,c_26])).

cnf(c_591,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_590])).

cnf(c_1723,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(sK3,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_3198,plain,
    ( r1_tsep_1(X0,sK2)
    | ~ r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_7939,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3198])).

cnf(c_7940,plain,
    ( r1_tsep_1(sK1,sK2) = iProver_top
    | r1_tsep_1(sK3,sK2) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7939])).

cnf(c_8261,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5004,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_5057,c_7081,c_7940])).

cnf(c_15,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1555,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8275,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8261,c_1555])).

cnf(c_9174,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9172,c_8275])).

cnf(c_1531,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X2) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_9270,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top
    | r1_tsep_1(sK1,X0) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9174,c_1531])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_844,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_26])).

cnf(c_845,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_849,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_28])).

cnf(c_850,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X1,X0)) ),
    inference(renaming,[status(thm)],[c_849])).

cnf(c_1636,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,sK2))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_1815,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_1816,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1815])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_869,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_870,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_874,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_870,c_28])).

cnf(c_875,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X1,X0),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_874])).

cnf(c_1654,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_1847,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_1848,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1847])).

cnf(c_12,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_361,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X0)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_362,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_366,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_28,c_26])).

cnf(c_367,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_1701,plain,
    ( r1_tsep_1(sK1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1904,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_1905,plain,
    ( r1_tsep_1(sK1,sK2) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1904])).

cnf(c_11,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_391,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_392,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_394,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_28,c_26])).

cnf(c_395,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_1717,plain,
    ( r1_tsep_1(sK1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),X0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_1930,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1717])).

cnf(c_1931,plain,
    ( r1_tsep_1(sK1,sK2) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_2789,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_7989,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2789])).

cnf(c_7995,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7989])).

cnf(c_8124,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2789])).

cnf(c_8130,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8124])).

cnf(c_1744,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(sK2,X0)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_3308,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,X0)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_11574,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3308])).

cnf(c_11575,plain,
    ( r1_tsep_1(sK2,sK1) != iProver_top
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11574])).

cnf(c_3460,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),X0) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_1529])).

cnf(c_1631,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,sK3))
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_1802,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_1803,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_1649,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_1834,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_1835,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(c_5965,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),X0) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_32,c_33,c_34,c_35,c_36,c_37,c_1803,c_1835])).

cnf(c_5966,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),X0) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5965])).

cnf(c_5975,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5966,c_1535])).

cnf(c_13,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X0,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_326,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X3,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X0,X3))
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_327,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X0,X2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_329,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X0,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_28,c_26])).

cnf(c_330,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X0,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_1542,plain,
    ( r1_tsep_1(X0,X1) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),k2_tsep_1(sK0,X0,X2)) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_8288,plain,
    ( r1_tsep_1(sK2,X0) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK2,X0),k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8261,c_1542])).

cnf(c_11720,plain,
    ( r1_tsep_1(sK2,X0) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK2,X0),k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8288,c_34,c_35,c_36,c_37])).

cnf(c_11727,plain,
    ( r1_tsep_1(sK2,sK1) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5118,c_11720])).

cnf(c_1963,plain,
    ( r1_tsep_1(sK1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),k2_tsep_1(sK0,X1,X0))
    | ~ m1_pre_topc(sK1,X1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_3615,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X0,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1963])).

cnf(c_4373,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3615])).

cnf(c_4374,plain,
    ( r1_tsep_1(sK1,sK2) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4373])).

cnf(c_11746,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11727,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_4374])).

cnf(c_8276,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8261,c_1553])).

cnf(c_1532,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X2,X1) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_8324,plain,
    ( r1_tsep_1(X0,sK1) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8276,c_1532])).

cnf(c_1809,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_1810,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1809])).

cnf(c_1841,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_1842,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1841])).

cnf(c_10374,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | r1_tsep_1(X0,sK1) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8324,c_32,c_33,c_34,c_35,c_36,c_37,c_1810,c_1842])).

cnf(c_10375,plain,
    ( r1_tsep_1(X0,sK1) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10374])).

cnf(c_11753,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11746,c_10375])).

cnf(c_13303,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5975,c_32,c_33,c_34,c_35,c_38,c_39,c_1816,c_1848,c_1905,c_8130,c_11753])).

cnf(c_16,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1554,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9181,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9172,c_1554])).

cnf(c_9248,plain,
    ( r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9181,c_1532])).

cnf(c_1641,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,sK1))
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_1819,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1641])).

cnf(c_1820,plain,
    ( m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1819])).

cnf(c_1659,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_1851,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_1852,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1851])).

cnf(c_13536,plain,
    ( r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9248,c_32,c_33,c_34,c_35,c_36,c_37,c_1820,c_1852])).

cnf(c_13546,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) = iProver_top
    | r1_tsep_1(sK2,sK1) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK1,sK3) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7036,c_13536])).

cnf(c_2,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_522,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_523,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_525,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_28,c_26])).

cnf(c_526,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_525])).

cnf(c_1687,plain,
    ( ~ r1_tsep_1(sK1,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_5497,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK1,X0))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,X0))
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_14784,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5497])).

cnf(c_14785,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14784])).

cnf(c_9269,plain,
    ( r1_tsep_1(X0,sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9174,c_1532])).

cnf(c_20507,plain,
    ( r1_tsep_1(X0,sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK2)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9269,c_32,c_33,c_34,c_35,c_36,c_37,c_1810,c_1842])).

cnf(c_20517,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11746,c_20507])).

cnf(c_20701,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9270,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_1816,c_1848,c_1905,c_1931,c_7995,c_8130,c_11575,c_11753,c_13546,c_14785,c_20517])).

cnf(c_20705,plain,
    ( r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_20701,c_1532])).

cnf(c_21016,plain,
    ( r1_tsep_1(X0,sK2) = iProver_top
    | m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20705,c_32,c_33,c_34,c_35,c_36,c_37,c_1820,c_1852])).

cnf(c_21026,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) = iProver_top
    | r1_tsep_1(sK2,sK1) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7036,c_21016])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21026,c_14785,c_13303,c_11575,c_7995,c_1931,c_1905,c_1848,c_1816,c_38,c_37,c_36,c_35,c_34,c_33,c_32])).


%------------------------------------------------------------------------------
