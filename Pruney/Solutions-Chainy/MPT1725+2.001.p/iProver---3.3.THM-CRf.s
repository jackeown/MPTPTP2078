%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:13 EST 2020

% Result     : Theorem 43.27s
% Output     : CNFRefutation 43.27s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_49)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49,f48,f47])).

fof(f87,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
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
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f40])).

cnf(c_25,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X0,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_356,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X3_42,X2_42)
    | ~ m1_pre_topc(X1_42,X3_42)
    | m1_pre_topc(k2_tsep_1(X2_42,X0_42,X1_42),k2_tsep_1(X2_42,X0_42,X3_42))
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(X3_42)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_21017,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(X0_42,X1_42)
    | m1_pre_topc(k2_tsep_1(X1_42,sK1,sK2),k2_tsep_1(X1_42,sK1,X0_42))
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK2,X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_150368,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_21017])).

cnf(c_12,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_367,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X2_42,X1_42)
    | ~ m1_pre_topc(X2_42,X0_42)
    | ~ m1_pre_topc(X0_42,X3_42)
    | ~ m1_pre_topc(X1_42,X3_42)
    | ~ m1_pre_topc(X2_42,X3_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(X3_42)
    | ~ l1_pre_topc(X3_42)
    | ~ v2_pre_topc(X3_42) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1831,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(k2_tsep_1(X2_42,X3_42,X4_42),X1_42)
    | ~ m1_pre_topc(X1_42,X5_42)
    | ~ m1_pre_topc(X0_42,X5_42)
    | ~ m1_pre_topc(X0_42,k2_tsep_1(X2_42,X3_42,X4_42))
    | ~ m1_pre_topc(k2_tsep_1(X2_42,X3_42,X4_42),X5_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X5_42)
    | v2_struct_0(k2_tsep_1(X2_42,X3_42,X4_42))
    | ~ l1_pre_topc(X5_42)
    | ~ v2_pre_topc(X5_42) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_8769,plain,
    ( r1_tsep_1(X0_42,sK2)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),X1_42)
    | ~ m1_pre_topc(sK2,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_150367,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),X0_42)
    | ~ m1_pre_topc(sK2,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_8769])).

cnf(c_150370,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_150367])).

cnf(c_17,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_362,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X3_42,X2_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(X3_42)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42)
    | k2_tsep_1(X2_42,X1_42,X0_42) = k2_tsep_1(X2_42,X0_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_349,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_14724,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tsep_1(sK0,X1_42,X0_42) = k2_tsep_1(sK0,X0_42,X1_42) ),
    inference(resolution,[status(thm)],[c_362,c_349])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_19192,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | k2_tsep_1(sK0,X1_42,X0_42) = k2_tsep_1(sK0,X0_42,X1_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14724,c_40,c_39,c_38,c_33])).

cnf(c_390,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X2_42,X3_42)
    | X2_42 != X0_42
    | X3_42 != X1_42 ),
    theory(equality)).

cnf(c_381,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_3242,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X2_42,X1_42)
    | X2_42 != X0_42 ),
    inference(resolution,[status(thm)],[c_390,c_381])).

cnf(c_19461,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X0_42,X1_42),X2_42)
    | r1_tsep_1(k2_tsep_1(sK0,X1_42,X0_42),X2_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42) ),
    inference(resolution,[status(thm)],[c_19192,c_3242])).

cnf(c_11407,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(sK3,X1_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_367,c_349])).

cnf(c_13793,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(sK3,X1_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11407,c_40,c_39,c_38,c_33])).

cnf(c_27,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_354,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_14762,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_13793,c_354])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_375,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X2_42,X1_42)
    | m1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42),X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ l1_pre_topc(X1_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2541,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_374,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X2_42,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,X2_42))
    | ~ l1_pre_topc(X1_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3557,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_6,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_373,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X1_42,X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2839,plain,
    ( ~ r1_tsep_1(X0_42,sK1)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_7412,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_7418,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7412])).

cnf(c_35942,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14762,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_2541,c_3557,c_7418,c_34967])).

cnf(c_35943,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_35942])).

cnf(c_39153,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_19461,c_35943])).

cnf(c_7,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_372,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3509,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_3516,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3509])).

cnf(c_39146,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_19461,c_354])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_70,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1913,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1725,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | X0_42 != k2_tsep_1(sK0,sK2,sK3)
    | X1_42 != sK1 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_1912,plain,
    ( r1_tsep_1(X0_42,sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | X0_42 != k2_tsep_1(sK0,sK2,sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_2284,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | k2_tsep_1(sK0,sK3,sK2) != k2_tsep_1(sK0,sK2,sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_2285,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tsep_1(sK0,sK3,sK2) = k2_tsep_1(sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_2289,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tsep_1(sK0,sK3,sK2) = k2_tsep_1(sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_345,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1044,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_1040,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_1027,plain,
    ( k2_tsep_1(X0_42,X1_42,X2_42) = k2_tsep_1(X0_42,X2_42,X1_42)
    | r1_tsep_1(X2_42,X1_42) = iProver_top
    | m1_pre_topc(X2_42,X0_42) != iProver_top
    | m1_pre_topc(X1_42,X0_42) != iProver_top
    | m1_pre_topc(X3_42,X0_42) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X2_42) = iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(X3_42) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top
    | v2_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_4388,plain,
    ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
    | r1_tsep_1(sK3,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | m1_pre_topc(X1_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1027])).

cnf(c_41,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_42,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_43,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_39344,plain,
    ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
    | r1_tsep_1(sK3,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | m1_pre_topc(X1_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X1_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4388,c_41,c_42,c_43,c_48])).

cnf(c_39356,plain,
    ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
    | r1_tsep_1(sK3,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_39344])).

cnf(c_39507,plain,
    ( v2_struct_0(X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | r1_tsep_1(sK3,X0_42) = iProver_top
    | k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39356,c_41,c_43,c_48,c_49,c_71,c_11093,c_39364])).

cnf(c_39508,plain,
    ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
    | r1_tsep_1(sK3,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top ),
    inference(renaming,[status(thm)],[c_39507])).

cnf(c_39517,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | r1_tsep_1(sK3,sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_39508])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_11,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_368,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X1_42,X2_42)
    | ~ m1_pre_topc(X2_42,X0_42)
    | ~ m1_pre_topc(X0_42,X3_42)
    | ~ m1_pre_topc(X1_42,X3_42)
    | ~ m1_pre_topc(X2_42,X3_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(X3_42)
    | ~ l1_pre_topc(X3_42)
    | ~ v2_pre_topc(X3_42) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2837,plain,
    ( ~ r1_tsep_1(X0_42,sK1)
    | r1_tsep_1(sK1,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X1_42,X0_42)
    | ~ m1_pre_topc(sK1,X2_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_16842,plain,
    ( r1_tsep_1(sK1,X0_42)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK3)
    | ~ m1_pre_topc(sK1,X1_42)
    | ~ m1_pre_topc(sK3,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_2837])).

cnf(c_34965,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_16842])).

cnf(c_34967,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_34965])).

cnf(c_39642,plain,
    ( r1_tsep_1(sK3,sK1)
    | v2_struct_0(sK1)
    | k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_39517])).

cnf(c_39965,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39517,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_7418,c_34967,c_39642])).

cnf(c_1035,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_39978,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_39965,c_1035])).

cnf(c_40055,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_39978])).

cnf(c_40418,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39146,c_40,c_39,c_38,c_35,c_34,c_33,c_32,c_70,c_1913,c_2284,c_2289,c_40055])).

cnf(c_9,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_370,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X0_42,X2_42)
    | ~ m1_pre_topc(X2_42,X1_42)
    | ~ m1_pre_topc(X0_42,X3_42)
    | ~ m1_pre_topc(X1_42,X3_42)
    | ~ m1_pre_topc(X2_42,X3_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(X3_42)
    | ~ l1_pre_topc(X3_42)
    | ~ v2_pre_topc(X3_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_14304,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X0_42,sK3)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | ~ m1_pre_topc(sK3,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_370,c_349])).

cnf(c_17875,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X0_42,sK3)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | ~ m1_pre_topc(sK3,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14304,c_40,c_39,c_38,c_33])).

cnf(c_29,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_352,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_18202,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_17875,c_352])).

cnf(c_30988,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18202,c_40,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_2541,c_3557])).

cnf(c_30989,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(renaming,[status(thm)],[c_30988])).

cnf(c_389,plain,
    ( X0_42 != X1_42
    | X2_42 != X3_42
    | X4_42 != X5_42
    | k2_tsep_1(X0_42,X2_42,X4_42) = k2_tsep_1(X1_42,X3_42,X5_42) ),
    theory(equality)).

cnf(c_3784,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
    | r1_tsep_1(k2_tsep_1(X4_42,X5_42,X6_42),X3_42)
    | X4_42 != X0_42
    | X5_42 != X1_42
    | X6_42 != X2_42 ),
    inference(resolution,[status(thm)],[c_3242,c_389])).

cnf(c_32153,plain,
    ( r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | X1_42 != sK2
    | X2_42 != sK3
    | X0_42 != sK0 ),
    inference(resolution,[status(thm)],[c_30989,c_3784])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_378,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ l1_pre_topc(X1_42)
    | l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1011,plain,
    ( m1_pre_topc(X0_42,X1_42) != iProver_top
    | l1_pre_topc(X1_42) != iProver_top
    | l1_pre_topc(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_1890,plain,
    ( l1_pre_topc(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1011])).

cnf(c_1902,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1890])).

cnf(c_361,plain,
    ( m1_pre_topc(X0_42,X0_42)
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2093,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_10,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_369,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(X2_42,X0_42)
    | ~ m1_pre_topc(X2_42,X1_42)
    | ~ m1_pre_topc(X0_42,X3_42)
    | ~ m1_pre_topc(X1_42,X3_42)
    | ~ m1_pre_topc(X2_42,X3_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(X3_42)
    | ~ l1_pre_topc(X3_42)
    | ~ v2_pre_topc(X3_42) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2836,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(X1_42,sK1)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X0_42,sK1)
    | ~ m1_pre_topc(sK1,X2_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_8446,plain,
    ( r1_tsep_1(X0_42,sK2)
    | ~ r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK1)
    | ~ m1_pre_topc(sK2,X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_2836])).

cnf(c_8974,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_8446])).

cnf(c_8976,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8974])).

cnf(c_39145,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(sK2,sK3)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_19461,c_352])).

cnf(c_39657,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(sK2,sK3)
    | m1_pre_topc(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39145,c_35,c_34,c_33,c_32])).

cnf(c_3504,plain,
    ( r1_tsep_1(sK2,X0_42)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK3)
    | ~ m1_pre_topc(sK2,X1_42)
    | ~ m1_pre_topc(sK3,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_105800,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_3504])).

cnf(c_105802,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_105800])).

cnf(c_106628,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32153,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_1902,c_2093,c_8976,c_39657,c_105802])).

cnf(c_126207,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39153,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_1902,c_2093,c_3516,c_8976,c_39657,c_40418,c_105802])).

cnf(c_126809,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK3,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_126207,c_13793])).

cnf(c_1967,plain,
    ( r1_tsep_1(sK2,X0_42)
    | ~ m1_pre_topc(X0_42,sK3)
    | ~ m1_pre_topc(X0_42,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK2,X0_42),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_2382,plain,
    ( r1_tsep_1(sK2,sK1)
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_20,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X0)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_359,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | m1_pre_topc(k2_tsep_1(X2_42,X0_42,X1_42),X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2073,plain,
    ( r1_tsep_1(sK1,X0_42)
    | ~ m1_pre_topc(X0_42,X1_42)
    | m1_pre_topc(k2_tsep_1(X1_42,sK1,X0_42),sK1)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_2757,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_2759,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2757])).

cnf(c_1813,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK1,X0_42)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_3261,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0_42)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_3264,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3261])).

cnf(c_386,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | m1_pre_topc(X2_42,X3_42)
    | X2_42 != X0_42
    | X3_42 != X1_42 ),
    theory(equality)).

cnf(c_2100,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | m1_pre_topc(X2_42,sK1)
    | X2_42 != X0_42
    | sK1 != X1_42 ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_2603,plain,
    ( ~ m1_pre_topc(X0_42,sK1)
    | m1_pre_topc(X1_42,sK1)
    | X1_42 != X0_42
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2100])).

cnf(c_4934,plain,
    ( m1_pre_topc(X0_42,sK1)
    | ~ m1_pre_topc(k2_tsep_1(X1_42,sK1,sK2),sK1)
    | X0_42 != k2_tsep_1(X1_42,sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_8921,plain,
    ( m1_pre_topc(k2_tsep_1(X0_42,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),sK1)
    | k2_tsep_1(X0_42,sK2,sK1) != k2_tsep_1(X0_42,sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4934])).

cnf(c_8924,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | k2_tsep_1(sK0,sK2,sK1) != k2_tsep_1(sK0,sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_8921])).

cnf(c_8922,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(sK2,X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42)
    | k2_tsep_1(X1_42,sK2,sK1) = k2_tsep_1(X1_42,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_8928,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tsep_1(sK0,sK2,sK1) = k2_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_8922])).

cnf(c_9157,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_26706,plain,
    ( ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | ~ v2_struct_0(k2_tsep_1(X0_42,sK2,sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_9157])).

cnf(c_26712,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_26706])).

cnf(c_6818,plain,
    ( ~ r1_tsep_1(X0_42,sK2)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(sK2,X1_42)
    | ~ m1_pre_topc(sK2,X0_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_28006,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_6818])).

cnf(c_28008,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_28006])).

cnf(c_11526,plain,
    ( ~ m1_pre_topc(X0_42,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK2,X0_42),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_29662,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11526])).

cnf(c_353,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_39149,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK1,sK3)
    | m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_19461,c_353])).

cnf(c_2764,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(sK1,X0_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X1_42,sK1)
    | ~ m1_pre_topc(sK1,X2_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_16881,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | r1_tsep_1(sK3,X0_42)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK1)
    | ~ m1_pre_topc(sK1,X1_42)
    | ~ m1_pre_topc(sK3,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_35228,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_16881])).

cnf(c_35230,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_35228])).

cnf(c_39717,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39149,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_1902,c_2093,c_7418,c_34967,c_35230])).

cnf(c_40474,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_40418,c_19461])).

cnf(c_2575,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_2581,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2575])).

cnf(c_1834,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(k2_tsep_1(X2_42,X3_42,X4_42),X5_42)
    | X1_42 != X5_42
    | X0_42 != k2_tsep_1(X2_42,X3_42,X4_42) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_2865,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(k2_tsep_1(X2_42,X3_42,X4_42),sK1)
    | X0_42 != k2_tsep_1(X2_42,X3_42,X4_42)
    | X1_42 != sK1 ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_6242,plain,
    ( r1_tsep_1(X0_42,sK1)
    | ~ r1_tsep_1(k2_tsep_1(X1_42,X2_42,X3_42),sK1)
    | X0_42 != k2_tsep_1(X1_42,X2_42,X3_42)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2865])).

cnf(c_10960,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),sK1)
    | r1_tsep_1(k2_tsep_1(X0_42,X2_42,X1_42),sK1)
    | k2_tsep_1(X0_42,X2_42,X1_42) != k2_tsep_1(X0_42,X1_42,X2_42)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_6242])).

cnf(c_36177,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | k2_tsep_1(sK0,sK2,sK3) != k2_tsep_1(sK0,sK3,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_10960])).

cnf(c_64363,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40474,c_40,c_39,c_38,c_35,c_34,c_33,c_32,c_70,c_1913,c_2581,c_36177,c_40055])).

cnf(c_64364,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_64363])).

cnf(c_2766,plain,
    ( ~ r1_tsep_1(sK1,X0_42)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK1)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_12163,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(X0_42,X1_42,X2_42))
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),sK1)
    | ~ m1_pre_topc(sK1,X3_42)
    | v2_struct_0(X3_42)
    | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X3_42)
    | ~ v2_pre_topc(X3_42) ),
    inference(instantiation,[status(thm)],[c_2766])).

cnf(c_38423,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(X0_42,X1_42,sK1))
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK1),X2_42)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK1),sK1)
    | ~ m1_pre_topc(sK1,X2_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(k2_tsep_1(X0_42,X1_42,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(instantiation,[status(thm)],[c_12163])).

cnf(c_129382,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0_42)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_38423])).

cnf(c_129384,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_129382])).

cnf(c_39714,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_39657,c_19461])).

cnf(c_9218,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),X0_42)
    | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_24649,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_9218])).

cnf(c_24651,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_24649])).

cnf(c_13847,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(sK1,X0_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_369,c_345])).

cnf(c_17820,plain,
    ( ~ r1_tsep_1(X0_42,X1_42)
    | r1_tsep_1(sK1,X0_42)
    | ~ m1_pre_topc(X0_42,sK0)
    | ~ m1_pre_topc(X1_42,sK0)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13847,c_40,c_39,c_38,c_37])).

cnf(c_17860,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_17820,c_352])).

cnf(c_2047,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_2050,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_2048,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),k2_tsep_1(sK0,sK2,sK3))
    | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_2265,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
    | ~ l1_pre_topc(X0_42)
    | l1_pre_topc(k2_tsep_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_2267,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | l1_pre_topc(k2_tsep_1(sK0,sK2,sK3))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2265])).

cnf(c_29596,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17860,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_29,c_2050,c_2048,c_2267,c_2541,c_3557])).

cnf(c_29597,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | m1_pre_topc(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_29596])).

cnf(c_39134,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | r1_tsep_1(sK3,sK2)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_19461,c_29597])).

cnf(c_48005,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(sK3,sK2)
    | m1_pre_topc(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39714,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_1902,c_2093,c_2541,c_3557,c_24651,c_39134])).

cnf(c_48546,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_48005,c_13793])).

cnf(c_6802,plain,
    ( ~ m1_pre_topc(X0_42,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0_42,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_14128,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6802])).

cnf(c_2762,plain,
    ( ~ r1_tsep_1(sK1,X0_42)
    | r1_tsep_1(sK1,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X1_42,X0_42)
    | ~ m1_pre_topc(sK1,X2_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_9219,plain,
    ( r1_tsep_1(sK1,X0_42)
    | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_2762])).

cnf(c_41629,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
    | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0_42)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_9219])).

cnf(c_41654,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
    | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_41629])).

cnf(c_347,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1042,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_4389,plain,
    ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
    | r1_tsep_1(sK2,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | m1_pre_topc(X1_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X1_42) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1027])).

cnf(c_46,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41831,plain,
    ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
    | r1_tsep_1(sK2,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | m1_pre_topc(X1_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(X1_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4389,c_41,c_42,c_43,c_46])).

cnf(c_41843,plain,
    ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
    | r1_tsep_1(sK2,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_41831])).

cnf(c_42300,plain,
    ( v2_struct_0(X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | r1_tsep_1(sK2,X0_42) = iProver_top
    | k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41843,c_48])).

cnf(c_42301,plain,
    ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
    | r1_tsep_1(sK2,X0_42) = iProver_top
    | m1_pre_topc(X0_42,sK0) != iProver_top
    | v2_struct_0(X0_42) = iProver_top ),
    inference(renaming,[status(thm)],[c_42300])).

cnf(c_42308,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(sK2,sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_42301])).

cnf(c_42434,plain,
    ( r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_42308])).

cnf(c_26715,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(sK2,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_102719,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_26715])).

cnf(c_106656,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_106628,c_17820])).

cnf(c_1863,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(X2_42,k2_tsep_1(X3_42,X4_42,X5_42))
    | X0_42 != X2_42
    | X1_42 != k2_tsep_1(X3_42,X4_42,X5_42) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_3114,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ r1_tsep_1(sK1,k2_tsep_1(X2_42,X3_42,X4_42))
    | X1_42 != k2_tsep_1(X2_42,X3_42,X4_42)
    | X0_42 != sK1 ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_7557,plain,
    ( r1_tsep_1(sK1,X0_42)
    | ~ r1_tsep_1(sK1,k2_tsep_1(X1_42,X2_42,X3_42))
    | X0_42 != k2_tsep_1(X1_42,X2_42,X3_42)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3114])).

cnf(c_10988,plain,
    ( ~ r1_tsep_1(sK1,k2_tsep_1(X0_42,X1_42,X2_42))
    | r1_tsep_1(sK1,k2_tsep_1(X0_42,X2_42,X1_42))
    | k2_tsep_1(X0_42,X2_42,X1_42) != k2_tsep_1(X0_42,X1_42,X2_42)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_7557])).

cnf(c_126476,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK3,sK2))
    | k2_tsep_1(sK0,sK2,sK3) != k2_tsep_1(sK0,sK3,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_10988])).

cnf(c_135865,plain,
    ( m1_pre_topc(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_48546,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_70,c_1902,c_1913,c_2093,c_2382,c_2541,c_2759,c_3557,c_8924,c_8928,c_8976,c_14128,c_26712,c_29662,c_41654,c_42434,c_102719,c_105802,c_106656,c_126476,c_129384])).

cnf(c_142183,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_126809,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_70,c_1902,c_1913,c_2093,c_2382,c_2541,c_2759,c_3264,c_3557,c_8924,c_8928,c_8976,c_14128,c_26712,c_28008,c_29662,c_39717,c_41654,c_42434,c_64364,c_102719,c_105802,c_106656,c_126476,c_129384])).

cnf(c_142233,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_142183,c_19461])).

cnf(c_1833,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
    | ~ m1_pre_topc(X3_42,X4_42)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X4_42)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
    | v2_struct_0(X3_42)
    | v2_struct_0(X4_42)
    | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
    | ~ l1_pre_topc(X4_42)
    | ~ v2_pre_topc(X4_42) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_6848,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),sK2)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),sK2)
    | ~ m1_pre_topc(sK2,X3_42)
    | v2_struct_0(X3_42)
    | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X3_42)
    | ~ v2_pre_topc(X3_42) ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_37923,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK2),X2_42)
    | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK2),sK2)
    | ~ m1_pre_topc(sK2,X2_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(k2_tsep_1(X0_42,X1_42,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(instantiation,[status(thm)],[c_6848])).

cnf(c_140899,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_37923])).

cnf(c_140901,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_140899])).

cnf(c_2838,plain,
    ( ~ r1_tsep_1(X0_42,sK1)
    | r1_tsep_1(X1_42,sK1)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | ~ m1_pre_topc(X1_42,X0_42)
    | ~ m1_pre_topc(sK1,X2_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_16841,plain,
    ( r1_tsep_1(X0_42,sK1)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,sK3)
    | ~ m1_pre_topc(sK1,X1_42)
    | ~ m1_pre_topc(sK3,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_34918,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,X0_42)
    | ~ m1_pre_topc(sK3,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_16841])).

cnf(c_34920,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_34918])).

cnf(c_9147,plain,
    ( ~ m1_pre_topc(X0_42,X1_42)
    | ~ m1_pre_topc(sK1,X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X1_42)
    | ~ v2_struct_0(k2_tsep_1(X1_42,sK1,X0_42))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_31229,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9147])).

cnf(c_11570,plain,
    ( ~ m1_pre_topc(X0_42,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0_42,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_29683,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11570])).

cnf(c_19609,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6802])).

cnf(c_8905,plain,
    ( ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | ~ v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_8907,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8905])).

cnf(c_19,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_360,plain,
    ( r1_tsep_1(X0_42,X1_42)
    | ~ m1_pre_topc(X0_42,X2_42)
    | ~ m1_pre_topc(X1_42,X2_42)
    | m1_pre_topc(k2_tsep_1(X2_42,X0_42,X1_42),X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(X2_42)
    | ~ l1_pre_topc(X2_42)
    | ~ v2_pre_topc(X2_42) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2342,plain,
    ( r1_tsep_1(X0_42,sK2)
    | ~ m1_pre_topc(X0_42,X1_42)
    | m1_pre_topc(k2_tsep_1(X1_42,X0_42,sK2),sK2)
    | ~ m1_pre_topc(sK2,X1_42)
    | v2_struct_0(X1_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_42)
    | ~ v2_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_6809,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,X0_42)
    | ~ m1_pre_topc(sK1,X0_42)
    | v2_struct_0(X0_42)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_42)
    | ~ v2_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_6811,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6809])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_150368,c_150370,c_142233,c_140901,c_135865,c_34920,c_31229,c_29683,c_19609,c_8976,c_8907,c_6811,c_2093,c_1902,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.27/6.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.27/6.01  
% 43.27/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.27/6.01  
% 43.27/6.01  ------  iProver source info
% 43.27/6.01  
% 43.27/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.27/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.27/6.01  git: non_committed_changes: false
% 43.27/6.01  git: last_make_outside_of_git: false
% 43.27/6.01  
% 43.27/6.01  ------ 
% 43.27/6.01  
% 43.27/6.01  ------ Input Options
% 43.27/6.01  
% 43.27/6.01  --out_options                           all
% 43.27/6.01  --tptp_safe_out                         true
% 43.27/6.01  --problem_path                          ""
% 43.27/6.01  --include_path                          ""
% 43.27/6.01  --clausifier                            res/vclausify_rel
% 43.27/6.01  --clausifier_options                    --mode clausify
% 43.27/6.01  --stdin                                 false
% 43.27/6.01  --stats_out                             sel
% 43.27/6.01  
% 43.27/6.01  ------ General Options
% 43.27/6.01  
% 43.27/6.01  --fof                                   false
% 43.27/6.01  --time_out_real                         604.99
% 43.27/6.01  --time_out_virtual                      -1.
% 43.27/6.01  --symbol_type_check                     false
% 43.27/6.01  --clausify_out                          false
% 43.27/6.01  --sig_cnt_out                           false
% 43.27/6.01  --trig_cnt_out                          false
% 43.27/6.01  --trig_cnt_out_tolerance                1.
% 43.27/6.01  --trig_cnt_out_sk_spl                   false
% 43.27/6.01  --abstr_cl_out                          false
% 43.27/6.01  
% 43.27/6.01  ------ Global Options
% 43.27/6.01  
% 43.27/6.01  --schedule                              none
% 43.27/6.01  --add_important_lit                     false
% 43.27/6.01  --prop_solver_per_cl                    1000
% 43.27/6.01  --min_unsat_core                        false
% 43.27/6.01  --soft_assumptions                      false
% 43.27/6.01  --soft_lemma_size                       3
% 43.27/6.01  --prop_impl_unit_size                   0
% 43.27/6.01  --prop_impl_unit                        []
% 43.27/6.01  --share_sel_clauses                     true
% 43.27/6.01  --reset_solvers                         false
% 43.27/6.01  --bc_imp_inh                            [conj_cone]
% 43.27/6.01  --conj_cone_tolerance                   3.
% 43.27/6.01  --extra_neg_conj                        none
% 43.27/6.01  --large_theory_mode                     true
% 43.27/6.01  --prolific_symb_bound                   200
% 43.27/6.01  --lt_threshold                          2000
% 43.27/6.01  --clause_weak_htbl                      true
% 43.27/6.01  --gc_record_bc_elim                     false
% 43.27/6.01  
% 43.27/6.01  ------ Preprocessing Options
% 43.27/6.01  
% 43.27/6.01  --preprocessing_flag                    true
% 43.27/6.01  --time_out_prep_mult                    0.1
% 43.27/6.01  --splitting_mode                        input
% 43.27/6.01  --splitting_grd                         true
% 43.27/6.01  --splitting_cvd                         false
% 43.27/6.01  --splitting_cvd_svl                     false
% 43.27/6.01  --splitting_nvd                         32
% 43.27/6.01  --sub_typing                            true
% 43.27/6.01  --prep_gs_sim                           false
% 43.27/6.01  --prep_unflatten                        true
% 43.27/6.01  --prep_res_sim                          true
% 43.27/6.01  --prep_upred                            true
% 43.27/6.01  --prep_sem_filter                       exhaustive
% 43.27/6.01  --prep_sem_filter_out                   false
% 43.27/6.01  --pred_elim                             false
% 43.27/6.01  --res_sim_input                         true
% 43.27/6.01  --eq_ax_congr_red                       true
% 43.27/6.01  --pure_diseq_elim                       true
% 43.27/6.01  --brand_transform                       false
% 43.27/6.01  --non_eq_to_eq                          false
% 43.27/6.01  --prep_def_merge                        true
% 43.27/6.01  --prep_def_merge_prop_impl              false
% 43.27/6.01  --prep_def_merge_mbd                    true
% 43.27/6.01  --prep_def_merge_tr_red                 false
% 43.27/6.01  --prep_def_merge_tr_cl                  false
% 43.27/6.01  --smt_preprocessing                     true
% 43.27/6.01  --smt_ac_axioms                         fast
% 43.27/6.01  --preprocessed_out                      false
% 43.27/6.01  --preprocessed_stats                    false
% 43.27/6.01  
% 43.27/6.01  ------ Abstraction refinement Options
% 43.27/6.01  
% 43.27/6.01  --abstr_ref                             []
% 43.27/6.01  --abstr_ref_prep                        false
% 43.27/6.01  --abstr_ref_until_sat                   false
% 43.27/6.01  --abstr_ref_sig_restrict                funpre
% 43.27/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.27/6.01  --abstr_ref_under                       []
% 43.27/6.01  
% 43.27/6.01  ------ SAT Options
% 43.27/6.01  
% 43.27/6.01  --sat_mode                              false
% 43.27/6.01  --sat_fm_restart_options                ""
% 43.27/6.01  --sat_gr_def                            false
% 43.27/6.01  --sat_epr_types                         true
% 43.27/6.01  --sat_non_cyclic_types                  false
% 43.27/6.01  --sat_finite_models                     false
% 43.27/6.01  --sat_fm_lemmas                         false
% 43.27/6.01  --sat_fm_prep                           false
% 43.27/6.01  --sat_fm_uc_incr                        true
% 43.27/6.01  --sat_out_model                         small
% 43.27/6.01  --sat_out_clauses                       false
% 43.27/6.01  
% 43.27/6.01  ------ QBF Options
% 43.27/6.01  
% 43.27/6.01  --qbf_mode                              false
% 43.27/6.01  --qbf_elim_univ                         false
% 43.27/6.01  --qbf_dom_inst                          none
% 43.27/6.01  --qbf_dom_pre_inst                      false
% 43.27/6.01  --qbf_sk_in                             false
% 43.27/6.01  --qbf_pred_elim                         true
% 43.27/6.01  --qbf_split                             512
% 43.27/6.01  
% 43.27/6.01  ------ BMC1 Options
% 43.27/6.01  
% 43.27/6.01  --bmc1_incremental                      false
% 43.27/6.01  --bmc1_axioms                           reachable_all
% 43.27/6.01  --bmc1_min_bound                        0
% 43.27/6.01  --bmc1_max_bound                        -1
% 43.27/6.01  --bmc1_max_bound_default                -1
% 43.27/6.01  --bmc1_symbol_reachability              true
% 43.27/6.01  --bmc1_property_lemmas                  false
% 43.27/6.01  --bmc1_k_induction                      false
% 43.27/6.01  --bmc1_non_equiv_states                 false
% 43.27/6.01  --bmc1_deadlock                         false
% 43.27/6.01  --bmc1_ucm                              false
% 43.27/6.01  --bmc1_add_unsat_core                   none
% 43.27/6.01  --bmc1_unsat_core_children              false
% 43.27/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.27/6.01  --bmc1_out_stat                         full
% 43.27/6.01  --bmc1_ground_init                      false
% 43.27/6.01  --bmc1_pre_inst_next_state              false
% 43.27/6.01  --bmc1_pre_inst_state                   false
% 43.27/6.01  --bmc1_pre_inst_reach_state             false
% 43.27/6.01  --bmc1_out_unsat_core                   false
% 43.27/6.01  --bmc1_aig_witness_out                  false
% 43.27/6.01  --bmc1_verbose                          false
% 43.27/6.01  --bmc1_dump_clauses_tptp                false
% 43.27/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.27/6.01  --bmc1_dump_file                        -
% 43.27/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.27/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.27/6.01  --bmc1_ucm_extend_mode                  1
% 43.27/6.01  --bmc1_ucm_init_mode                    2
% 43.27/6.01  --bmc1_ucm_cone_mode                    none
% 43.27/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.27/6.01  --bmc1_ucm_relax_model                  4
% 43.27/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.27/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.27/6.01  --bmc1_ucm_layered_model                none
% 43.27/6.01  --bmc1_ucm_max_lemma_size               10
% 43.27/6.01  
% 43.27/6.01  ------ AIG Options
% 43.27/6.01  
% 43.27/6.01  --aig_mode                              false
% 43.27/6.01  
% 43.27/6.01  ------ Instantiation Options
% 43.27/6.01  
% 43.27/6.01  --instantiation_flag                    true
% 43.27/6.01  --inst_sos_flag                         false
% 43.27/6.01  --inst_sos_phase                        true
% 43.27/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.27/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.27/6.01  --inst_lit_sel_side                     num_symb
% 43.27/6.01  --inst_solver_per_active                1400
% 43.27/6.01  --inst_solver_calls_frac                1.
% 43.27/6.01  --inst_passive_queue_type               priority_queues
% 43.27/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.27/6.01  --inst_passive_queues_freq              [25;2]
% 43.27/6.01  --inst_dismatching                      true
% 43.27/6.01  --inst_eager_unprocessed_to_passive     true
% 43.27/6.01  --inst_prop_sim_given                   true
% 43.27/6.01  --inst_prop_sim_new                     false
% 43.27/6.01  --inst_subs_new                         false
% 43.27/6.01  --inst_eq_res_simp                      false
% 43.27/6.01  --inst_subs_given                       false
% 43.27/6.01  --inst_orphan_elimination               true
% 43.27/6.01  --inst_learning_loop_flag               true
% 43.27/6.01  --inst_learning_start                   3000
% 43.27/6.01  --inst_learning_factor                  2
% 43.27/6.01  --inst_start_prop_sim_after_learn       3
% 43.27/6.01  --inst_sel_renew                        solver
% 43.27/6.01  --inst_lit_activity_flag                true
% 43.27/6.01  --inst_restr_to_given                   false
% 43.27/6.01  --inst_activity_threshold               500
% 43.27/6.01  --inst_out_proof                        true
% 43.27/6.01  
% 43.27/6.01  ------ Resolution Options
% 43.27/6.01  
% 43.27/6.01  --resolution_flag                       true
% 43.27/6.01  --res_lit_sel                           adaptive
% 43.27/6.01  --res_lit_sel_side                      none
% 43.27/6.01  --res_ordering                          kbo
% 43.27/6.01  --res_to_prop_solver                    active
% 43.27/6.01  --res_prop_simpl_new                    false
% 43.27/6.01  --res_prop_simpl_given                  true
% 43.27/6.01  --res_passive_queue_type                priority_queues
% 43.27/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.27/6.01  --res_passive_queues_freq               [15;5]
% 43.27/6.01  --res_forward_subs                      full
% 43.27/6.01  --res_backward_subs                     full
% 43.27/6.01  --res_forward_subs_resolution           true
% 43.27/6.01  --res_backward_subs_resolution          true
% 43.27/6.01  --res_orphan_elimination                true
% 43.27/6.01  --res_time_limit                        2.
% 43.27/6.01  --res_out_proof                         true
% 43.27/6.01  
% 43.27/6.01  ------ Superposition Options
% 43.27/6.01  
% 43.27/6.01  --superposition_flag                    true
% 43.27/6.01  --sup_passive_queue_type                priority_queues
% 43.27/6.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.27/6.01  --sup_passive_queues_freq               [1;4]
% 43.27/6.01  --demod_completeness_check              fast
% 43.27/6.01  --demod_use_ground                      true
% 43.27/6.01  --sup_to_prop_solver                    passive
% 43.27/6.01  --sup_prop_simpl_new                    true
% 43.27/6.01  --sup_prop_simpl_given                  true
% 43.27/6.01  --sup_fun_splitting                     false
% 43.27/6.01  --sup_smt_interval                      50000
% 43.27/6.01  
% 43.27/6.01  ------ Superposition Simplification Setup
% 43.27/6.01  
% 43.27/6.01  --sup_indices_passive                   []
% 43.27/6.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.27/6.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.27/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.27/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.27/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.27/6.01  --sup_full_bw                           [BwDemod]
% 43.27/6.01  --sup_immed_triv                        [TrivRules]
% 43.27/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.27/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.27/6.01  --sup_immed_bw_main                     []
% 43.27/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.27/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.27/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.27/6.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.27/6.01  
% 43.27/6.01  ------ Combination Options
% 43.27/6.01  
% 43.27/6.01  --comb_res_mult                         3
% 43.27/6.01  --comb_sup_mult                         2
% 43.27/6.01  --comb_inst_mult                        10
% 43.27/6.01  
% 43.27/6.01  ------ Debug Options
% 43.27/6.01  
% 43.27/6.01  --dbg_backtrace                         false
% 43.27/6.01  --dbg_dump_prop_clauses                 false
% 43.27/6.01  --dbg_dump_prop_clauses_file            -
% 43.27/6.01  --dbg_out_stat                          false
% 43.27/6.01  ------ Parsing...
% 43.27/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.27/6.01  
% 43.27/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.27/6.01  
% 43.27/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.27/6.01  
% 43.27/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/6.01  ------ Proving...
% 43.27/6.01  ------ Problem Properties 
% 43.27/6.01  
% 43.27/6.01  
% 43.27/6.01  clauses                                 41
% 43.27/6.01  conjectures                             14
% 43.27/6.01  EPR                                     20
% 43.27/6.01  Horn                                    13
% 43.27/6.01  unary                                   10
% 43.27/6.01  binary                                  2
% 43.27/6.01  lits                                    269
% 43.27/6.01  lits eq                                 8
% 43.27/6.01  fd_pure                                 0
% 43.27/6.01  fd_pseudo                               0
% 43.27/6.01  fd_cond                                 0
% 43.27/6.01  fd_pseudo_cond                          0
% 43.27/6.01  AC symbols                              0
% 43.27/6.01  
% 43.27/6.01  ------ Input Options Time Limit: Unbounded
% 43.27/6.01  
% 43.27/6.01  
% 43.27/6.01  ------ 
% 43.27/6.01  Current options:
% 43.27/6.01  ------ 
% 43.27/6.01  
% 43.27/6.01  ------ Input Options
% 43.27/6.01  
% 43.27/6.01  --out_options                           all
% 43.27/6.01  --tptp_safe_out                         true
% 43.27/6.01  --problem_path                          ""
% 43.27/6.01  --include_path                          ""
% 43.27/6.01  --clausifier                            res/vclausify_rel
% 43.27/6.01  --clausifier_options                    --mode clausify
% 43.27/6.01  --stdin                                 false
% 43.27/6.01  --stats_out                             sel
% 43.27/6.01  
% 43.27/6.01  ------ General Options
% 43.27/6.01  
% 43.27/6.01  --fof                                   false
% 43.27/6.01  --time_out_real                         604.99
% 43.27/6.01  --time_out_virtual                      -1.
% 43.27/6.01  --symbol_type_check                     false
% 43.27/6.01  --clausify_out                          false
% 43.27/6.01  --sig_cnt_out                           false
% 43.27/6.01  --trig_cnt_out                          false
% 43.27/6.01  --trig_cnt_out_tolerance                1.
% 43.27/6.01  --trig_cnt_out_sk_spl                   false
% 43.27/6.01  --abstr_cl_out                          false
% 43.27/6.01  
% 43.27/6.01  ------ Global Options
% 43.27/6.01  
% 43.27/6.01  --schedule                              none
% 43.27/6.01  --add_important_lit                     false
% 43.27/6.01  --prop_solver_per_cl                    1000
% 43.27/6.01  --min_unsat_core                        false
% 43.27/6.01  --soft_assumptions                      false
% 43.27/6.01  --soft_lemma_size                       3
% 43.27/6.01  --prop_impl_unit_size                   0
% 43.27/6.01  --prop_impl_unit                        []
% 43.27/6.01  --share_sel_clauses                     true
% 43.27/6.01  --reset_solvers                         false
% 43.27/6.01  --bc_imp_inh                            [conj_cone]
% 43.27/6.01  --conj_cone_tolerance                   3.
% 43.27/6.01  --extra_neg_conj                        none
% 43.27/6.01  --large_theory_mode                     true
% 43.27/6.01  --prolific_symb_bound                   200
% 43.27/6.01  --lt_threshold                          2000
% 43.27/6.01  --clause_weak_htbl                      true
% 43.27/6.01  --gc_record_bc_elim                     false
% 43.27/6.01  
% 43.27/6.01  ------ Preprocessing Options
% 43.27/6.01  
% 43.27/6.01  --preprocessing_flag                    true
% 43.27/6.01  --time_out_prep_mult                    0.1
% 43.27/6.01  --splitting_mode                        input
% 43.27/6.01  --splitting_grd                         true
% 43.27/6.01  --splitting_cvd                         false
% 43.27/6.01  --splitting_cvd_svl                     false
% 43.27/6.01  --splitting_nvd                         32
% 43.27/6.01  --sub_typing                            true
% 43.27/6.01  --prep_gs_sim                           false
% 43.27/6.01  --prep_unflatten                        true
% 43.27/6.01  --prep_res_sim                          true
% 43.27/6.01  --prep_upred                            true
% 43.27/6.01  --prep_sem_filter                       exhaustive
% 43.27/6.01  --prep_sem_filter_out                   false
% 43.27/6.01  --pred_elim                             false
% 43.27/6.01  --res_sim_input                         true
% 43.27/6.01  --eq_ax_congr_red                       true
% 43.27/6.01  --pure_diseq_elim                       true
% 43.27/6.01  --brand_transform                       false
% 43.27/6.01  --non_eq_to_eq                          false
% 43.27/6.01  --prep_def_merge                        true
% 43.27/6.01  --prep_def_merge_prop_impl              false
% 43.27/6.01  --prep_def_merge_mbd                    true
% 43.27/6.01  --prep_def_merge_tr_red                 false
% 43.27/6.01  --prep_def_merge_tr_cl                  false
% 43.27/6.01  --smt_preprocessing                     true
% 43.27/6.01  --smt_ac_axioms                         fast
% 43.27/6.01  --preprocessed_out                      false
% 43.27/6.01  --preprocessed_stats                    false
% 43.27/6.01  
% 43.27/6.01  ------ Abstraction refinement Options
% 43.27/6.01  
% 43.27/6.01  --abstr_ref                             []
% 43.27/6.01  --abstr_ref_prep                        false
% 43.27/6.01  --abstr_ref_until_sat                   false
% 43.27/6.01  --abstr_ref_sig_restrict                funpre
% 43.27/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.27/6.01  --abstr_ref_under                       []
% 43.27/6.01  
% 43.27/6.01  ------ SAT Options
% 43.27/6.01  
% 43.27/6.01  --sat_mode                              false
% 43.27/6.01  --sat_fm_restart_options                ""
% 43.27/6.01  --sat_gr_def                            false
% 43.27/6.01  --sat_epr_types                         true
% 43.27/6.01  --sat_non_cyclic_types                  false
% 43.27/6.01  --sat_finite_models                     false
% 43.27/6.01  --sat_fm_lemmas                         false
% 43.27/6.01  --sat_fm_prep                           false
% 43.27/6.01  --sat_fm_uc_incr                        true
% 43.27/6.01  --sat_out_model                         small
% 43.27/6.01  --sat_out_clauses                       false
% 43.27/6.01  
% 43.27/6.01  ------ QBF Options
% 43.27/6.01  
% 43.27/6.01  --qbf_mode                              false
% 43.27/6.01  --qbf_elim_univ                         false
% 43.27/6.01  --qbf_dom_inst                          none
% 43.27/6.01  --qbf_dom_pre_inst                      false
% 43.27/6.01  --qbf_sk_in                             false
% 43.27/6.01  --qbf_pred_elim                         true
% 43.27/6.01  --qbf_split                             512
% 43.27/6.01  
% 43.27/6.01  ------ BMC1 Options
% 43.27/6.01  
% 43.27/6.01  --bmc1_incremental                      false
% 43.27/6.01  --bmc1_axioms                           reachable_all
% 43.27/6.01  --bmc1_min_bound                        0
% 43.27/6.01  --bmc1_max_bound                        -1
% 43.27/6.01  --bmc1_max_bound_default                -1
% 43.27/6.01  --bmc1_symbol_reachability              true
% 43.27/6.01  --bmc1_property_lemmas                  false
% 43.27/6.01  --bmc1_k_induction                      false
% 43.27/6.01  --bmc1_non_equiv_states                 false
% 43.27/6.01  --bmc1_deadlock                         false
% 43.27/6.01  --bmc1_ucm                              false
% 43.27/6.01  --bmc1_add_unsat_core                   none
% 43.27/6.01  --bmc1_unsat_core_children              false
% 43.27/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.27/6.01  --bmc1_out_stat                         full
% 43.27/6.01  --bmc1_ground_init                      false
% 43.27/6.01  --bmc1_pre_inst_next_state              false
% 43.27/6.01  --bmc1_pre_inst_state                   false
% 43.27/6.01  --bmc1_pre_inst_reach_state             false
% 43.27/6.01  --bmc1_out_unsat_core                   false
% 43.27/6.01  --bmc1_aig_witness_out                  false
% 43.27/6.01  --bmc1_verbose                          false
% 43.27/6.01  --bmc1_dump_clauses_tptp                false
% 43.27/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.27/6.01  --bmc1_dump_file                        -
% 43.27/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.27/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.27/6.01  --bmc1_ucm_extend_mode                  1
% 43.27/6.01  --bmc1_ucm_init_mode                    2
% 43.27/6.01  --bmc1_ucm_cone_mode                    none
% 43.27/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.27/6.01  --bmc1_ucm_relax_model                  4
% 43.27/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.27/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.27/6.01  --bmc1_ucm_layered_model                none
% 43.27/6.01  --bmc1_ucm_max_lemma_size               10
% 43.27/6.01  
% 43.27/6.01  ------ AIG Options
% 43.27/6.01  
% 43.27/6.01  --aig_mode                              false
% 43.27/6.01  
% 43.27/6.01  ------ Instantiation Options
% 43.27/6.01  
% 43.27/6.01  --instantiation_flag                    true
% 43.27/6.01  --inst_sos_flag                         false
% 43.27/6.01  --inst_sos_phase                        true
% 43.27/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.27/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.27/6.01  --inst_lit_sel_side                     num_symb
% 43.27/6.01  --inst_solver_per_active                1400
% 43.27/6.01  --inst_solver_calls_frac                1.
% 43.27/6.01  --inst_passive_queue_type               priority_queues
% 43.27/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.27/6.01  --inst_passive_queues_freq              [25;2]
% 43.27/6.01  --inst_dismatching                      true
% 43.27/6.01  --inst_eager_unprocessed_to_passive     true
% 43.27/6.01  --inst_prop_sim_given                   true
% 43.27/6.01  --inst_prop_sim_new                     false
% 43.27/6.01  --inst_subs_new                         false
% 43.27/6.01  --inst_eq_res_simp                      false
% 43.27/6.01  --inst_subs_given                       false
% 43.27/6.01  --inst_orphan_elimination               true
% 43.27/6.01  --inst_learning_loop_flag               true
% 43.27/6.01  --inst_learning_start                   3000
% 43.27/6.01  --inst_learning_factor                  2
% 43.27/6.01  --inst_start_prop_sim_after_learn       3
% 43.27/6.01  --inst_sel_renew                        solver
% 43.27/6.01  --inst_lit_activity_flag                true
% 43.27/6.01  --inst_restr_to_given                   false
% 43.27/6.01  --inst_activity_threshold               500
% 43.27/6.01  --inst_out_proof                        true
% 43.27/6.01  
% 43.27/6.01  ------ Resolution Options
% 43.27/6.01  
% 43.27/6.01  --resolution_flag                       true
% 43.27/6.01  --res_lit_sel                           adaptive
% 43.27/6.01  --res_lit_sel_side                      none
% 43.27/6.01  --res_ordering                          kbo
% 43.27/6.01  --res_to_prop_solver                    active
% 43.27/6.01  --res_prop_simpl_new                    false
% 43.27/6.01  --res_prop_simpl_given                  true
% 43.27/6.01  --res_passive_queue_type                priority_queues
% 43.27/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.27/6.01  --res_passive_queues_freq               [15;5]
% 43.27/6.01  --res_forward_subs                      full
% 43.27/6.01  --res_backward_subs                     full
% 43.27/6.01  --res_forward_subs_resolution           true
% 43.27/6.01  --res_backward_subs_resolution          true
% 43.27/6.01  --res_orphan_elimination                true
% 43.27/6.01  --res_time_limit                        2.
% 43.27/6.01  --res_out_proof                         true
% 43.27/6.01  
% 43.27/6.01  ------ Superposition Options
% 43.27/6.01  
% 43.27/6.01  --superposition_flag                    true
% 43.27/6.01  --sup_passive_queue_type                priority_queues
% 43.27/6.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.27/6.01  --sup_passive_queues_freq               [1;4]
% 43.27/6.01  --demod_completeness_check              fast
% 43.27/6.01  --demod_use_ground                      true
% 43.27/6.01  --sup_to_prop_solver                    passive
% 43.27/6.01  --sup_prop_simpl_new                    true
% 43.27/6.01  --sup_prop_simpl_given                  true
% 43.27/6.01  --sup_fun_splitting                     false
% 43.27/6.01  --sup_smt_interval                      50000
% 43.27/6.01  
% 43.27/6.01  ------ Superposition Simplification Setup
% 43.27/6.01  
% 43.27/6.01  --sup_indices_passive                   []
% 43.27/6.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.27/6.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.27/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.27/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.27/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.27/6.01  --sup_full_bw                           [BwDemod]
% 43.27/6.01  --sup_immed_triv                        [TrivRules]
% 43.27/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.27/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.27/6.01  --sup_immed_bw_main                     []
% 43.27/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.27/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.27/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.27/6.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.27/6.01  
% 43.27/6.01  ------ Combination Options
% 43.27/6.01  
% 43.27/6.01  --comb_res_mult                         3
% 43.27/6.01  --comb_sup_mult                         2
% 43.27/6.01  --comb_inst_mult                        10
% 43.27/6.01  
% 43.27/6.01  ------ Debug Options
% 43.27/6.01  
% 43.27/6.01  --dbg_backtrace                         false
% 43.27/6.01  --dbg_dump_prop_clauses                 false
% 43.27/6.01  --dbg_dump_prop_clauses_file            -
% 43.27/6.01  --dbg_out_stat                          false
% 43.27/6.01  
% 43.27/6.01  
% 43.27/6.01  
% 43.27/6.01  
% 43.27/6.01  ------ Proving...
% 43.27/6.01  
% 43.27/6.01  
% 43.27/6.01  % SZS status Theorem for theBenchmark.p
% 43.27/6.01  
% 43.27/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.27/6.01  
% 43.27/6.01  fof(f14,axiom,(
% 43.27/6.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f43,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 43.27/6.01    inference(ennf_transformation,[],[f14])).
% 43.27/6.01  
% 43.27/6.01  fof(f44,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 43.27/6.01    inference(flattening,[],[f43])).
% 43.27/6.01  
% 43.27/6.01  fof(f78,plain,(
% 43.27/6.01    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f44])).
% 43.27/6.01  
% 43.27/6.01  fof(f7,axiom,(
% 43.27/6.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f30,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 43.27/6.01    inference(ennf_transformation,[],[f7])).
% 43.27/6.01  
% 43.27/6.01  fof(f31,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 43.27/6.01    inference(flattening,[],[f30])).
% 43.27/6.01  
% 43.27/6.01  fof(f61,plain,(
% 43.27/6.01    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f31])).
% 43.27/6.01  
% 43.27/6.01  fof(f10,axiom,(
% 43.27/6.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((((~r1_tsep_1(X1,k2_tsep_1(X0,X2,X3)) & ~r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2))) => k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3)) & (~r1_tsep_1(X1,X2) => k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)))))))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f36,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) | ((r1_tsep_1(X1,k2_tsep_1(X0,X2,X3)) | r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))) & (k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) | r1_tsep_1(X1,X2))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 43.27/6.01    inference(ennf_transformation,[],[f10])).
% 43.27/6.01  
% 43.27/6.01  fof(f37,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) | ((r1_tsep_1(X1,k2_tsep_1(X0,X2,X3)) | r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))) & (k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) | r1_tsep_1(X1,X2))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 43.27/6.01    inference(flattening,[],[f36])).
% 43.27/6.01  
% 43.27/6.01  fof(f67,plain,(
% 43.27/6.01    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f37])).
% 43.27/6.01  
% 43.27/6.01  fof(f15,conjecture,(
% 43.27/6.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f16,negated_conjecture,(
% 43.27/6.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 43.27/6.01    inference(negated_conjecture,[],[f15])).
% 43.27/6.01  
% 43.27/6.01  fof(f45,plain,(
% 43.27/6.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 43.27/6.01    inference(ennf_transformation,[],[f16])).
% 43.27/6.01  
% 43.27/6.01  fof(f46,plain,(
% 43.27/6.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 43.27/6.01    inference(flattening,[],[f45])).
% 43.27/6.01  
% 43.27/6.01  fof(f50,plain,(
% 43.27/6.01    ( ! [X2,X0,X1] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((((r1_tsep_1(k2_tsep_1(X0,sK3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,sK3),X2)) & m1_pre_topc(X2,sK3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,sK3),X1) | r1_tsep_1(k2_tsep_1(X0,sK3,X2),X1)) & m1_pre_topc(X1,sK3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 43.27/6.01    introduced(choice_axiom,[])).
% 43.27/6.01  
% 43.27/6.01  fof(f49,plain,(
% 43.27/6.01    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),sK2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),sK2)) & m1_pre_topc(sK2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,sK2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,sK2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 43.27/6.01    introduced(choice_axiom,[])).
% 43.27/6.01  
% 43.27/6.01  fof(f48,plain,(
% 43.27/6.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,sK1),X2) | r1_tsep_1(k2_tsep_1(X0,sK1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),sK1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 43.27/6.01    introduced(choice_axiom,[])).
% 43.27/6.01  
% 43.27/6.01  fof(f47,plain,(
% 43.27/6.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 43.27/6.01    introduced(choice_axiom,[])).
% 43.27/6.01  
% 43.27/6.01  fof(f51,plain,(
% 43.27/6.01    ((((((r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)) & m1_pre_topc(sK2,sK3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 43.27/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49,f48,f47])).
% 43.27/6.01  
% 43.27/6.01  fof(f87,plain,(
% 43.27/6.01    m1_pre_topc(sK3,sK0)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f79,plain,(
% 43.27/6.01    ~v2_struct_0(sK0)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f80,plain,(
% 43.27/6.01    v2_pre_topc(sK0)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f81,plain,(
% 43.27/6.01    l1_pre_topc(sK0)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f86,plain,(
% 43.27/6.01    ~v2_struct_0(sK3)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f92,plain,(
% 43.27/6.01    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f82,plain,(
% 43.27/6.01    ~v2_struct_0(sK1)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f83,plain,(
% 43.27/6.01    m1_pre_topc(sK1,sK0)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f84,plain,(
% 43.27/6.01    ~v2_struct_0(sK2)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f85,plain,(
% 43.27/6.01    m1_pre_topc(sK2,sK0)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f91,plain,(
% 43.27/6.01    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | m1_pre_topc(sK1,sK3)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f4,axiom,(
% 43.27/6.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f17,plain,(
% 43.27/6.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 43.27/6.01    inference(pure_predicate_removal,[],[f4])).
% 43.27/6.01  
% 43.27/6.01  fof(f24,plain,(
% 43.27/6.01    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 43.27/6.01    inference(ennf_transformation,[],[f17])).
% 43.27/6.01  
% 43.27/6.01  fof(f25,plain,(
% 43.27/6.01    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 43.27/6.01    inference(flattening,[],[f24])).
% 43.27/6.01  
% 43.27/6.01  fof(f57,plain,(
% 43.27/6.01    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f25])).
% 43.27/6.01  
% 43.27/6.01  fof(f56,plain,(
% 43.27/6.01    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f25])).
% 43.27/6.01  
% 43.27/6.01  fof(f5,axiom,(
% 43.27/6.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f26,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 43.27/6.01    inference(ennf_transformation,[],[f5])).
% 43.27/6.01  
% 43.27/6.01  fof(f27,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 43.27/6.01    inference(flattening,[],[f26])).
% 43.27/6.01  
% 43.27/6.01  fof(f59,plain,(
% 43.27/6.01    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f27])).
% 43.27/6.01  
% 43.27/6.01  fof(f58,plain,(
% 43.27/6.01    ( ! [X2,X0,X1] : (~r1_tsep_1(X1,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f27])).
% 43.27/6.01  
% 43.27/6.01  fof(f11,axiom,(
% 43.27/6.01    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f38,plain,(
% 43.27/6.01    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 43.27/6.01    inference(ennf_transformation,[],[f11])).
% 43.27/6.01  
% 43.27/6.01  fof(f70,plain,(
% 43.27/6.01    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f38])).
% 43.27/6.01  
% 43.27/6.01  fof(f88,plain,(
% 43.27/6.01    ~r1_tsep_1(sK1,sK2)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f89,plain,(
% 43.27/6.01    m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f62,plain,(
% 43.27/6.01    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X2,X3) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f31])).
% 43.27/6.01  
% 43.27/6.01  fof(f64,plain,(
% 43.27/6.01    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f31])).
% 43.27/6.01  
% 43.27/6.01  fof(f90,plain,(
% 43.27/6.01    m1_pre_topc(sK2,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 43.27/6.01    inference(cnf_transformation,[],[f51])).
% 43.27/6.01  
% 43.27/6.01  fof(f2,axiom,(
% 43.27/6.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f21,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 43.27/6.01    inference(ennf_transformation,[],[f2])).
% 43.27/6.01  
% 43.27/6.01  fof(f53,plain,(
% 43.27/6.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f21])).
% 43.27/6.01  
% 43.27/6.01  fof(f63,plain,(
% 43.27/6.01    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,X2) | r1_tsep_1(X1,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f31])).
% 43.27/6.01  
% 43.27/6.01  fof(f12,axiom,(
% 43.27/6.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 43.27/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.27/6.01  
% 43.27/6.01  fof(f39,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 43.27/6.01    inference(ennf_transformation,[],[f12])).
% 43.27/6.01  
% 43.27/6.01  fof(f40,plain,(
% 43.27/6.01    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 43.27/6.01    inference(flattening,[],[f39])).
% 43.27/6.01  
% 43.27/6.01  fof(f71,plain,(
% 43.27/6.01    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f40])).
% 43.27/6.01  
% 43.27/6.01  fof(f72,plain,(
% 43.27/6.01    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 43.27/6.01    inference(cnf_transformation,[],[f40])).
% 43.27/6.01  
% 43.27/6.01  cnf(c_25,plain,
% 43.27/6.01      ( r1_tsep_1(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X0,X2)
% 43.27/6.01      | ~ m1_pre_topc(X1,X2)
% 43.27/6.01      | ~ m1_pre_topc(X3,X2)
% 43.27/6.01      | ~ m1_pre_topc(X1,X3)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X0,X3))
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | v2_struct_0(X3)
% 43.27/6.01      | ~ l1_pre_topc(X2)
% 43.27/6.01      | ~ v2_pre_topc(X2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f78]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_356,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X3_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X3_42)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X2_42,X0_42,X1_42),k2_tsep_1(X2_42,X0_42,X3_42))
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_25]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_21017,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X1_42,sK1,sK2),k2_tsep_1(X1_42,sK1,X0_42))
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_356]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_150368,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_21017]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_12,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0,X1)
% 43.27/6.01      | r1_tsep_1(X2,X1)
% 43.27/6.01      | ~ m1_pre_topc(X2,X3)
% 43.27/6.01      | ~ m1_pre_topc(X0,X3)
% 43.27/6.01      | ~ m1_pre_topc(X2,X0)
% 43.27/6.01      | ~ m1_pre_topc(X1,X3)
% 43.27/6.01      | v2_struct_0(X3)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | ~ l1_pre_topc(X3)
% 43.27/6.01      | ~ v2_pre_topc(X3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f61]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_367,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X2_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X3_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | ~ l1_pre_topc(X3_42)
% 43.27/6.01      | ~ v2_pre_topc(X3_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_12]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1831,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(X2_42,X3_42,X4_42),X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X5_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X5_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,k2_tsep_1(X2_42,X3_42,X4_42))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X2_42,X3_42,X4_42),X5_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X5_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(X2_42,X3_42,X4_42))
% 43.27/6.01      | ~ l1_pre_topc(X5_42)
% 43.27/6.01      | ~ v2_pre_topc(X5_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_367]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8769,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,sK2)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1831]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_150367,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_8769]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_150370,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_150367]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_17,plain,
% 43.27/6.01      ( r1_tsep_1(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X0,X2)
% 43.27/6.01      | ~ m1_pre_topc(X1,X2)
% 43.27/6.01      | ~ m1_pre_topc(X3,X2)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | v2_struct_0(X3)
% 43.27/6.01      | ~ l1_pre_topc(X2)
% 43.27/6.01      | ~ v2_pre_topc(X2)
% 43.27/6.01      | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X0,X1) ),
% 43.27/6.01      inference(cnf_transformation,[],[f67]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_362,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X3_42,X2_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42)
% 43.27/6.01      | k2_tsep_1(X2_42,X1_42,X0_42) = k2_tsep_1(X2_42,X0_42,X1_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_17]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_32,negated_conjecture,
% 43.27/6.01      ( m1_pre_topc(sK3,sK0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f87]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_349,negated_conjecture,
% 43.27/6.01      ( m1_pre_topc(sK3,sK0) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_32]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_14724,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0)
% 43.27/6.01      | k2_tsep_1(sK0,X1_42,X0_42) = k2_tsep_1(sK0,X0_42,X1_42) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_362,c_349]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_40,negated_conjecture,
% 43.27/6.01      ( ~ v2_struct_0(sK0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f79]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39,negated_conjecture,
% 43.27/6.01      ( v2_pre_topc(sK0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f80]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_38,negated_conjecture,
% 43.27/6.01      ( l1_pre_topc(sK0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f81]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_33,negated_conjecture,
% 43.27/6.01      ( ~ v2_struct_0(sK3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f86]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_19192,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | k2_tsep_1(sK0,X1_42,X0_42) = k2_tsep_1(sK0,X0_42,X1_42) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_14724,c_40,c_39,c_38,c_33]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_390,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X2_42,X3_42)
% 43.27/6.01      | X2_42 != X0_42
% 43.27/6.01      | X3_42 != X1_42 ),
% 43.27/6.01      theory(equality) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_381,plain,( X0_42 = X0_42 ),theory(equality) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3242,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X2_42,X1_42)
% 43.27/6.01      | X2_42 != X0_42 ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_390,c_381]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_19461,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(sK0,X0_42,X1_42),X2_42)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,X1_42,X0_42),X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_19192,c_3242]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_11407,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(sK3,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_367,c_349]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_13793,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(sK3,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_11407,c_40,c_39,c_38,c_33]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_27,negated_conjecture,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f92]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_354,negated_conjecture,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_27]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_14762,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_13793,c_354]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_37,negated_conjecture,
% 43.27/6.01      ( ~ v2_struct_0(sK1) ),
% 43.27/6.01      inference(cnf_transformation,[],[f82]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_36,negated_conjecture,
% 43.27/6.01      ( m1_pre_topc(sK1,sK0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f83]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_35,negated_conjecture,
% 43.27/6.01      ( ~ v2_struct_0(sK2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f84]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_34,negated_conjecture,
% 43.27/6.01      ( m1_pre_topc(sK2,sK0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f85]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_28,negated_conjecture,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | m1_pre_topc(sK1,sK3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f91]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_4,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X2,X1)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | ~ l1_pre_topc(X1) ),
% 43.27/6.01      inference(cnf_transformation,[],[f57]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_375,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X1_42)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X1_42,X0_42,X2_42),X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | ~ l1_pre_topc(X1_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_4]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2541,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_375]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_5,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X2,X1)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 43.27/6.01      | ~ l1_pre_topc(X1) ),
% 43.27/6.01      inference(cnf_transformation,[],[f56]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_374,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,X2_42))
% 43.27/6.01      | ~ l1_pre_topc(X1_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_5]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3557,plain,
% 43.27/6.01      ( ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_374]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_6,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X1,X2)
% 43.27/6.01      | ~ m1_pre_topc(X0,X2)
% 43.27/6.01      | ~ m1_pre_topc(X1,X0)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | ~ l1_pre_topc(X2)
% 43.27/6.01      | ~ v2_pre_topc(X2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f59]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_373,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_6]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2839,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_373]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_7412,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2839]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_7418,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_7412]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_35942,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3)) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_14762,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_31,c_30,c_2541,c_3557,c_7418,c_34967]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_35943,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3)) ),
% 43.27/6.01      inference(renaming,[status(thm)],[c_35942]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39153,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK1,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_19461,c_35943]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_7,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X0,X2)
% 43.27/6.01      | ~ m1_pre_topc(X1,X2)
% 43.27/6.01      | ~ m1_pre_topc(X0,X1)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | ~ l1_pre_topc(X2)
% 43.27/6.01      | ~ v2_pre_topc(X2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f58]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_372,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_7]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3509,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_372]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3516,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_3509]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39146,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_19461,c_354]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_18,plain,
% 43.27/6.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f70]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_70,plain,
% 43.27/6.01      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_18]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1913,plain,
% 43.27/6.01      ( sK1 = sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_381]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1725,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | X0_42 != k2_tsep_1(sK0,sK2,sK3)
% 43.27/6.01      | X1_42 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_390]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1912,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,sK1)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | X0_42 != k2_tsep_1(sK0,sK2,sK3)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1725]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2284,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | k2_tsep_1(sK0,sK3,sK2) != k2_tsep_1(sK0,sK2,sK3)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1912]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2285,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0)
% 43.27/6.01      | k2_tsep_1(sK0,sK3,sK2) = k2_tsep_1(sK0,sK2,sK3) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_362]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2289,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK0,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0)
% 43.27/6.01      | k2_tsep_1(sK0,sK3,sK2) = k2_tsep_1(sK0,sK2,sK3) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2285]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_345,negated_conjecture,
% 43.27/6.01      ( m1_pre_topc(sK1,sK0) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_36]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1044,plain,
% 43.27/6.01      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1040,plain,
% 43.27/6.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1027,plain,
% 43.27/6.01      ( k2_tsep_1(X0_42,X1_42,X2_42) = k2_tsep_1(X0_42,X2_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X2_42,X1_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X2_42,X0_42) != iProver_top
% 43.27/6.01      | m1_pre_topc(X1_42,X0_42) != iProver_top
% 43.27/6.01      | m1_pre_topc(X3_42,X0_42) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | v2_struct_0(X2_42) = iProver_top
% 43.27/6.01      | v2_struct_0(X1_42) = iProver_top
% 43.27/6.01      | v2_struct_0(X3_42) = iProver_top
% 43.27/6.01      | l1_pre_topc(X0_42) != iProver_top
% 43.27/6.01      | v2_pre_topc(X0_42) != iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_4388,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | m1_pre_topc(X1_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | v2_struct_0(X1_42) = iProver_top
% 43.27/6.01      | v2_struct_0(sK3) = iProver_top
% 43.27/6.01      | v2_struct_0(sK0) = iProver_top
% 43.27/6.01      | l1_pre_topc(sK0) != iProver_top
% 43.27/6.01      | v2_pre_topc(sK0) != iProver_top ),
% 43.27/6.01      inference(superposition,[status(thm)],[c_1040,c_1027]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_41,plain,
% 43.27/6.01      ( v2_struct_0(sK0) != iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_42,plain,
% 43.27/6.01      ( v2_pre_topc(sK0) = iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_43,plain,
% 43.27/6.01      ( l1_pre_topc(sK0) = iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_48,plain,
% 43.27/6.01      ( v2_struct_0(sK3) != iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39344,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | m1_pre_topc(X1_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | v2_struct_0(X1_42) = iProver_top ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_4388,c_41,c_42,c_43,c_48]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39356,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | v2_struct_0(sK3) = iProver_top ),
% 43.27/6.01      inference(superposition,[status(thm)],[c_1040,c_39344]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39507,plain,
% 43.27/6.01      ( v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | r1_tsep_1(sK3,X0_42) = iProver_top
% 43.27/6.01      | k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_39356,c_41,c_43,c_48,c_49,c_71,c_11093,c_39364]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39508,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,sK3,X0_42) = k2_tsep_1(sK0,X0_42,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top ),
% 43.27/6.01      inference(renaming,[status(thm)],[c_39507]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39517,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,sK1) = iProver_top
% 43.27/6.01      | v2_struct_0(sK1) = iProver_top ),
% 43.27/6.01      inference(superposition,[status(thm)],[c_1044,c_39508]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_31,negated_conjecture,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,sK2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f88]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_30,negated_conjecture,
% 43.27/6.01      ( m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f89]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_11,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0,X1)
% 43.27/6.01      | r1_tsep_1(X1,X2)
% 43.27/6.01      | ~ m1_pre_topc(X2,X3)
% 43.27/6.01      | ~ m1_pre_topc(X0,X3)
% 43.27/6.01      | ~ m1_pre_topc(X2,X0)
% 43.27/6.01      | ~ m1_pre_topc(X1,X3)
% 43.27/6.01      | v2_struct_0(X3)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | ~ l1_pre_topc(X3)
% 43.27/6.01      | ~ v2_pre_topc(X3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f62]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_368,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X3_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | ~ l1_pre_topc(X3_42)
% 43.27/6.01      | ~ v2_pre_topc(X3_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_11]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2837,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,sK1)
% 43.27/6.01      | r1_tsep_1(sK1,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X2_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_368]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_16842,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2837]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_34965,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_16842]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_34967,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_34965]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39642,plain,
% 43.27/6.01      ( r1_tsep_1(sK3,sK1)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
% 43.27/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_39517]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39965,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_39517,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_31,c_30,c_7418,c_34967,c_39642]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1035,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39978,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) = iProver_top
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) = iProver_top ),
% 43.27/6.01      inference(demodulation,[status(thm)],[c_39965,c_1035]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_40055,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
% 43.27/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_39978]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_40418,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK2,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_39146,c_40,c_39,c_38,c_35,c_34,c_33,c_32,c_70,c_1913,
% 43.27/6.01                 c_2284,c_2289,c_40055]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_9,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0,X1)
% 43.27/6.01      | r1_tsep_1(X0,X2)
% 43.27/6.01      | ~ m1_pre_topc(X2,X3)
% 43.27/6.01      | ~ m1_pre_topc(X1,X3)
% 43.27/6.01      | ~ m1_pre_topc(X2,X1)
% 43.27/6.01      | ~ m1_pre_topc(X0,X3)
% 43.27/6.01      | v2_struct_0(X3)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | ~ l1_pre_topc(X3)
% 43.27/6.01      | ~ v2_pre_topc(X3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f64]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_370,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X3_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | ~ l1_pre_topc(X3_42)
% 43.27/6.01      | ~ v2_pre_topc(X3_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_9]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_14304,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X0_42,sK3)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_370,c_349]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_17875,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X0_42,sK3)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_14304,c_40,c_39,c_38,c_33]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_29,negated_conjecture,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f90]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_352,negated_conjecture,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_29]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_18202,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK3)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK1)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_17875,c_352]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_30988,plain,
% 43.27/6.01      ( m1_pre_topc(sK2,sK3)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK3)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK1) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_18202,c_40,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_2541,
% 43.27/6.01                 c_3557]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_30989,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK3)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK1) ),
% 43.27/6.01      inference(renaming,[status(thm)],[c_30988]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_389,plain,
% 43.27/6.01      ( X0_42 != X1_42
% 43.27/6.01      | X2_42 != X3_42
% 43.27/6.01      | X4_42 != X5_42
% 43.27/6.01      | k2_tsep_1(X0_42,X2_42,X4_42) = k2_tsep_1(X1_42,X3_42,X5_42) ),
% 43.27/6.01      theory(equality) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3784,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(X4_42,X5_42,X6_42),X3_42)
% 43.27/6.01      | X4_42 != X0_42
% 43.27/6.01      | X5_42 != X1_42
% 43.27/6.01      | X6_42 != X2_42 ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_3242,c_389]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_32153,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),sK3)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK1)
% 43.27/6.01      | X1_42 != sK2
% 43.27/6.01      | X2_42 != sK3
% 43.27/6.01      | X0_42 != sK0 ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_30989,c_3784]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 43.27/6.01      inference(cnf_transformation,[],[f53]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_378,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | l1_pre_topc(X0_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_1]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1011,plain,
% 43.27/6.01      ( m1_pre_topc(X0_42,X1_42) != iProver_top
% 43.27/6.01      | l1_pre_topc(X1_42) != iProver_top
% 43.27/6.01      | l1_pre_topc(X0_42) = iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1890,plain,
% 43.27/6.01      ( l1_pre_topc(sK1) = iProver_top
% 43.27/6.01      | l1_pre_topc(sK0) != iProver_top ),
% 43.27/6.01      inference(superposition,[status(thm)],[c_1044,c_1011]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1902,plain,
% 43.27/6.01      ( l1_pre_topc(sK1) | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_1890]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_361,plain,
% 43.27/6.01      ( m1_pre_topc(X0_42,X0_42) | ~ l1_pre_topc(X0_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_18]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2093,plain,
% 43.27/6.01      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_361]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_10,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0,X1)
% 43.27/6.01      | r1_tsep_1(X2,X0)
% 43.27/6.01      | ~ m1_pre_topc(X2,X3)
% 43.27/6.01      | ~ m1_pre_topc(X1,X3)
% 43.27/6.01      | ~ m1_pre_topc(X2,X1)
% 43.27/6.01      | ~ m1_pre_topc(X0,X3)
% 43.27/6.01      | v2_struct_0(X3)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | ~ l1_pre_topc(X3)
% 43.27/6.01      | ~ v2_pre_topc(X3) ),
% 43.27/6.01      inference(cnf_transformation,[],[f63]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_369,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(X2_42,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X2_42,X3_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | ~ l1_pre_topc(X3_42)
% 43.27/6.01      | ~ v2_pre_topc(X3_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_10]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2836,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(X1_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X2_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_369]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8446,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,sK2)
% 43.27/6.01      | ~ r1_tsep_1(sK2,sK1)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2836]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8974,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK2,sK1)
% 43.27/6.01      | r1_tsep_1(sK1,sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_8446]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8976,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK2,sK1)
% 43.27/6.01      | r1_tsep_1(sK1,sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_8974]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39145,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(sK2,sK3)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_19461,c_352]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39657,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(sK2,sK3)
% 43.27/6.01      | m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_39145,c_35,c_34,c_33,c_32]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3504,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,X0_42)
% 43.27/6.01      | ~ r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_370]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_105800,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK1)
% 43.27/6.01      | ~ r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_3504]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_105802,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK1)
% 43.27/6.01      | ~ r1_tsep_1(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_105800]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_106628,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) | m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_32153,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_31,c_30,c_1902,c_2093,c_8976,c_39657,c_105802]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_126207,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_39153,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_31,c_30,c_1902,c_2093,c_3516,c_8976,c_39657,c_40418,
% 43.27/6.01                 c_105802]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_126809,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK3,sK2))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
% 43.27/6.01      | v2_struct_0(sK1) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_126207,c_13793]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1967,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK3)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,sK2,X0_42),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_356]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2382,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK1)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1967]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_20,plain,
% 43.27/6.01      ( r1_tsep_1(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X0,X2)
% 43.27/6.01      | ~ m1_pre_topc(X1,X2)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X2,X0,X1),X0)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | ~ l1_pre_topc(X2)
% 43.27/6.01      | ~ v2_pre_topc(X2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f71]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_359,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X2_42,X0_42,X1_42),X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_20]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2073,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X1_42,sK1,X0_42),sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_359]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2757,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2073]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2759,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2757]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1813,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_368]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3261,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1813]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3264,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_3261]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_386,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | m1_pre_topc(X2_42,X3_42)
% 43.27/6.01      | X2_42 != X0_42
% 43.27/6.01      | X3_42 != X1_42 ),
% 43.27/6.01      theory(equality) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2100,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | m1_pre_topc(X2_42,sK1)
% 43.27/6.01      | X2_42 != X0_42
% 43.27/6.01      | sK1 != X1_42 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_386]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2603,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,sK1)
% 43.27/6.01      | m1_pre_topc(X1_42,sK1)
% 43.27/6.01      | X1_42 != X0_42
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2100]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_4934,plain,
% 43.27/6.01      ( m1_pre_topc(X0_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X1_42,sK1,sK2),sK1)
% 43.27/6.01      | X0_42 != k2_tsep_1(X1_42,sK1,sK2)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2603]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8921,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(X0_42,sK2,sK1),sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),sK1)
% 43.27/6.01      | k2_tsep_1(X0_42,sK2,sK1) != k2_tsep_1(X0_42,sK1,sK2)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_4934]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8924,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
% 43.27/6.01      | k2_tsep_1(sK0,sK2,sK1) != k2_tsep_1(sK0,sK1,sK2)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_8921]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8922,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42)
% 43.27/6.01      | k2_tsep_1(X1_42,sK2,sK1) = k2_tsep_1(X1_42,sK1,sK2) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_362]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8928,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK0,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0)
% 43.27/6.01      | k2_tsep_1(sK0,sK2,sK1) = k2_tsep_1(sK0,sK1,sK2) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_8922]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_9157,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,sK1))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_374]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_26706,plain,
% 43.27/6.01      ( ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(X0_42,sK2,sK1))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_9157]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_26712,plain,
% 43.27/6.01      ( ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_26706]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_6818,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,sK2)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_373]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_28006,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK3,sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_6818]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_28008,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK3,sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_28006]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_11526,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,sK2,X0_42),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_375]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_29662,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_11526]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_353,negated_conjecture,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | m1_pre_topc(sK1,sK3) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_28]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39149,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK1,sK3)
% 43.27/6.01      | m1_pre_topc(sK1,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_19461,c_353]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2764,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X2_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_368]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_16881,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2764]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_35228,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_16881]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_35230,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_35228]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39717,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | m1_pre_topc(sK1,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_39149,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_31,c_30,c_1902,c_2093,c_7418,c_34967,c_35230]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_40474,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK2,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_40418,c_19461]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2575,plain,
% 43.27/6.01      ( r1_tsep_1(sK3,sK2)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0)
% 43.27/6.01      | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_362]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2581,plain,
% 43.27/6.01      ( r1_tsep_1(sK3,sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK0,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0)
% 43.27/6.01      | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2575]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1834,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(X2_42,X3_42,X4_42),X5_42)
% 43.27/6.01      | X1_42 != X5_42
% 43.27/6.01      | X0_42 != k2_tsep_1(X2_42,X3_42,X4_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_390]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2865,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(X2_42,X3_42,X4_42),sK1)
% 43.27/6.01      | X0_42 != k2_tsep_1(X2_42,X3_42,X4_42)
% 43.27/6.01      | X1_42 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1834]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_6242,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,sK1)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(X1_42,X2_42,X3_42),sK1)
% 43.27/6.01      | X0_42 != k2_tsep_1(X1_42,X2_42,X3_42)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2865]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_10960,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(X0_42,X2_42,X1_42),sK1)
% 43.27/6.01      | k2_tsep_1(X0_42,X2_42,X1_42) != k2_tsep_1(X0_42,X1_42,X2_42)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_6242]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_36177,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | k2_tsep_1(sK0,sK2,sK3) != k2_tsep_1(sK0,sK3,sK2)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_10960]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_64363,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK3,sK2) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_40474,c_40,c_39,c_38,c_35,c_34,c_33,c_32,c_70,c_1913,
% 43.27/6.01                 c_2581,c_36177,c_40055]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_64364,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 43.27/6.01      | r1_tsep_1(sK3,sK2) ),
% 43.27/6.01      inference(renaming,[status(thm)],[c_64363]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2766,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_373]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_12163,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,k2_tsep_1(X0_42,X1_42,X2_42))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X3_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X3_42)
% 43.27/6.01      | ~ v2_pre_topc(X3_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2766]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_38423,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,k2_tsep_1(X0_42,X1_42,sK1))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK1),X2_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK1),sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X2_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(X0_42,X1_42,sK1))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_12163]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_129382,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_38423]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_129384,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_129382]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39714,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK2,sK3)
% 43.27/6.01      | r1_tsep_1(sK3,sK2)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_39657,c_19461]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_9218,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),X0_42)
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2764]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_24649,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_9218]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_24651,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_24649]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_13847,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_369,c_345]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_17820,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_13847,c_40,c_39,c_38,c_37]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_17860,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_17820,c_352]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2047,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1813]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2050,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2047]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2048,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ l1_pre_topc(k2_tsep_1(sK0,sK2,sK3)) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_361]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2265,plain,
% 43.27/6.01      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | l1_pre_topc(k2_tsep_1(sK0,sK2,sK3)) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_378]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2267,plain,
% 43.27/6.01      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | l1_pre_topc(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2265]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_29596,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_17860,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_29,c_2050,c_2048,c_2267,c_2541,c_3557]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_29597,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(renaming,[status(thm)],[c_29596]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_39134,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | r1_tsep_1(sK3,sK2)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_19461,c_29597]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_48005,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 43.27/6.01      | r1_tsep_1(sK3,sK2)
% 43.27/6.01      | m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_39714,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_1902,c_2093,c_2541,c_3557,c_24651,c_39134]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_48546,plain,
% 43.27/6.01      ( r1_tsep_1(sK3,sK2)
% 43.27/6.01      | r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_48005,c_13793]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_6802,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,X0_42,sK2),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_375]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_14128,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_6802]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2762,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | r1_tsep_1(sK1,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X2_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_370]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_9219,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2762]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_41629,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_9219]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_41654,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_41629]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_347,negated_conjecture,
% 43.27/6.01      ( m1_pre_topc(sK2,sK0) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_34]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1042,plain,
% 43.27/6.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_4389,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
% 43.27/6.01      | r1_tsep_1(sK2,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | m1_pre_topc(X1_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | v2_struct_0(X1_42) = iProver_top
% 43.27/6.01      | v2_struct_0(sK2) = iProver_top
% 43.27/6.01      | v2_struct_0(sK0) = iProver_top
% 43.27/6.01      | l1_pre_topc(sK0) != iProver_top
% 43.27/6.01      | v2_pre_topc(sK0) != iProver_top ),
% 43.27/6.01      inference(superposition,[status(thm)],[c_1042,c_1027]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_46,plain,
% 43.27/6.01      ( v2_struct_0(sK2) != iProver_top ),
% 43.27/6.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_41831,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
% 43.27/6.01      | r1_tsep_1(sK2,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | m1_pre_topc(X1_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | v2_struct_0(X1_42) = iProver_top ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_4389,c_41,c_42,c_43,c_46]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_41843,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
% 43.27/6.01      | r1_tsep_1(sK2,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | v2_struct_0(sK3) = iProver_top ),
% 43.27/6.01      inference(superposition,[status(thm)],[c_1040,c_41831]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_42300,plain,
% 43.27/6.01      ( v2_struct_0(X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | r1_tsep_1(sK2,X0_42) = iProver_top
% 43.27/6.01      | k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_41843,c_48]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_42301,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,X0_42,sK2) = k2_tsep_1(sK0,sK2,X0_42)
% 43.27/6.01      | r1_tsep_1(sK2,X0_42) = iProver_top
% 43.27/6.01      | m1_pre_topc(X0_42,sK0) != iProver_top
% 43.27/6.01      | v2_struct_0(X0_42) = iProver_top ),
% 43.27/6.01      inference(renaming,[status(thm)],[c_42300]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_42308,plain,
% 43.27/6.01      ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
% 43.27/6.01      | r1_tsep_1(sK2,sK3) = iProver_top
% 43.27/6.01      | v2_struct_0(sK3) = iProver_top ),
% 43.27/6.01      inference(superposition,[status(thm)],[c_1040,c_42301]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_42434,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK3)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
% 43.27/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_42308]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_26715,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(X1_42,X0_42,sK2))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_374]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_102719,plain,
% 43.27/6.01      ( ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_26715]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_106656,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK3,sK2))
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
% 43.27/6.01      | m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
% 43.27/6.01      | v2_struct_0(sK1) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_106628,c_17820]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1863,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(X2_42,k2_tsep_1(X3_42,X4_42,X5_42))
% 43.27/6.01      | X0_42 != X2_42
% 43.27/6.01      | X1_42 != k2_tsep_1(X3_42,X4_42,X5_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_390]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_3114,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(X2_42,X3_42,X4_42))
% 43.27/6.01      | X1_42 != k2_tsep_1(X2_42,X3_42,X4_42)
% 43.27/6.01      | X0_42 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1863]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_7557,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,X0_42)
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(X1_42,X2_42,X3_42))
% 43.27/6.01      | X0_42 != k2_tsep_1(X1_42,X2_42,X3_42)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_3114]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_10988,plain,
% 43.27/6.01      ( ~ r1_tsep_1(sK1,k2_tsep_1(X0_42,X1_42,X2_42))
% 43.27/6.01      | r1_tsep_1(sK1,k2_tsep_1(X0_42,X2_42,X1_42))
% 43.27/6.01      | k2_tsep_1(X0_42,X2_42,X1_42) != k2_tsep_1(X0_42,X1_42,X2_42)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_7557]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_126476,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK2,sK3))
% 43.27/6.01      | ~ r1_tsep_1(sK1,k2_tsep_1(sK0,sK3,sK2))
% 43.27/6.01      | k2_tsep_1(sK0,sK2,sK3) != k2_tsep_1(sK0,sK3,sK2)
% 43.27/6.01      | sK1 != sK1 ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_10988]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_135865,plain,
% 43.27/6.01      ( m1_pre_topc(sK2,sK3) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_48546,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_31,c_30,c_70,c_1902,c_1913,c_2093,c_2382,c_2541,
% 43.27/6.01                 c_2759,c_3557,c_8924,c_8928,c_8976,c_14128,c_26712,
% 43.27/6.01                 c_29662,c_41654,c_42434,c_102719,c_105802,c_106656,
% 43.27/6.01                 c_126476,c_129384]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_142183,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
% 43.27/6.01      inference(global_propositional_subsumption,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_126809,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,
% 43.27/6.01                 c_31,c_30,c_70,c_1902,c_1913,c_2093,c_2382,c_2541,
% 43.27/6.01                 c_2759,c_3264,c_3557,c_8924,c_8928,c_8976,c_14128,
% 43.27/6.01                 c_26712,c_28008,c_29662,c_39717,c_41654,c_42434,c_64364,
% 43.27/6.01                 c_102719,c_105802,c_106656,c_126476,c_129384]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_142233,plain,
% 43.27/6.01      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 43.27/6.01      | r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3) ),
% 43.27/6.01      inference(resolution,[status(thm)],[c_142183,c_19461]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_1833,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
% 43.27/6.01      | ~ m1_pre_topc(X3_42,X4_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X4_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | v2_struct_0(X4_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
% 43.27/6.01      | ~ l1_pre_topc(X4_42)
% 43.27/6.01      | ~ v2_pre_topc(X4_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_372]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_6848,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,X2_42),sK2)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),X3_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,X2_42),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X3_42)
% 43.27/6.01      | v2_struct_0(X3_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(X0_42,X1_42,X2_42))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X3_42)
% 43.27/6.01      | ~ v2_pre_topc(X3_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_1833]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_37923,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(X0_42,X1_42,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK2),X2_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(X0_42,X1_42,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X2_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(X0_42,X1_42,sK2))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_6848]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_140899,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0_42)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_37923]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_140901,plain,
% 43.27/6.01      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_140899]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2838,plain,
% 43.27/6.01      ( ~ r1_tsep_1(X0_42,sK1)
% 43.27/6.01      | r1_tsep_1(X1_42,sK1)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X2_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_367]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_16841,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,sK1)
% 43.27/6.01      | ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2838]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_34918,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK1)
% 43.27/6.01      | ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK3,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_16841]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_34920,plain,
% 43.27/6.01      ( r1_tsep_1(sK2,sK1)
% 43.27/6.01      | ~ r1_tsep_1(sK3,sK1)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK3)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_34918]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_9147,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(X1_42,sK1,X0_42))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_374]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_31229,plain,
% 43.27/6.01      ( ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_9147]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_11570,plain,
% 43.27/6.01      ( ~ m1_pre_topc(X0_42,sK0)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,X0_42,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_375]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_29683,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK3,sK0)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK3)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_11570]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_19609,plain,
% 43.27/6.01      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_6802]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8905,plain,
% 43.27/6.01      ( ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(X0_42,sK1,sK2))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_374]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_8907,plain,
% 43.27/6.01      ( ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_8905]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_19,plain,
% 43.27/6.01      ( r1_tsep_1(X0,X1)
% 43.27/6.01      | ~ m1_pre_topc(X0,X2)
% 43.27/6.01      | ~ m1_pre_topc(X1,X2)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X2,X0,X1),X1)
% 43.27/6.01      | v2_struct_0(X2)
% 43.27/6.01      | v2_struct_0(X0)
% 43.27/6.01      | v2_struct_0(X1)
% 43.27/6.01      | ~ l1_pre_topc(X2)
% 43.27/6.01      | ~ v2_pre_topc(X2) ),
% 43.27/6.01      inference(cnf_transformation,[],[f72]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_360,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,X1_42)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X2_42)
% 43.27/6.01      | ~ m1_pre_topc(X1_42,X2_42)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X2_42,X0_42,X1_42),X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(X2_42)
% 43.27/6.01      | ~ l1_pre_topc(X2_42)
% 43.27/6.01      | ~ v2_pre_topc(X2_42) ),
% 43.27/6.01      inference(subtyping,[status(esa)],[c_19]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_2342,plain,
% 43.27/6.01      ( r1_tsep_1(X0_42,sK2)
% 43.27/6.01      | ~ m1_pre_topc(X0_42,X1_42)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X1_42,X0_42,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X1_42)
% 43.27/6.01      | v2_struct_0(X1_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | ~ l1_pre_topc(X1_42)
% 43.27/6.01      | ~ v2_pre_topc(X1_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_360]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_6809,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(X0_42,sK1,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,X0_42)
% 43.27/6.01      | ~ m1_pre_topc(sK1,X0_42)
% 43.27/6.01      | v2_struct_0(X0_42)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | ~ l1_pre_topc(X0_42)
% 43.27/6.01      | ~ v2_pre_topc(X0_42) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_2342]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(c_6811,plain,
% 43.27/6.01      ( r1_tsep_1(sK1,sK2)
% 43.27/6.01      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
% 43.27/6.01      | ~ m1_pre_topc(sK2,sK0)
% 43.27/6.01      | ~ m1_pre_topc(sK1,sK0)
% 43.27/6.01      | v2_struct_0(sK2)
% 43.27/6.01      | v2_struct_0(sK1)
% 43.27/6.01      | v2_struct_0(sK0)
% 43.27/6.01      | ~ l1_pre_topc(sK0)
% 43.27/6.01      | ~ v2_pre_topc(sK0) ),
% 43.27/6.01      inference(instantiation,[status(thm)],[c_6809]) ).
% 43.27/6.01  
% 43.27/6.01  cnf(contradiction,plain,
% 43.27/6.01      ( $false ),
% 43.27/6.01      inference(minisat,
% 43.27/6.01                [status(thm)],
% 43.27/6.01                [c_150368,c_150370,c_142233,c_140901,c_135865,c_34920,
% 43.27/6.01                 c_31229,c_29683,c_19609,c_8976,c_8907,c_6811,c_2093,
% 43.27/6.01                 c_1902,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,
% 43.27/6.01                 c_40]) ).
% 43.27/6.01  
% 43.27/6.01  
% 43.27/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.27/6.01  
% 43.27/6.01  ------                               Statistics
% 43.27/6.01  
% 43.27/6.01  ------ Selected
% 43.27/6.01  
% 43.27/6.01  total_time:                             5.249
% 43.27/6.01  
%------------------------------------------------------------------------------
