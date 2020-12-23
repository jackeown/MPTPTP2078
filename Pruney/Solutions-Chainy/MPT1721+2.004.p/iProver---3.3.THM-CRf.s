%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:11 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  171 (1546 expanded)
%              Number of clauses        :  111 ( 338 expanded)
%              Number of leaves         :   13 ( 576 expanded)
%              Depth                    :   25
%              Number of atoms          :  922 (17183 expanded)
%              Number of equality atoms :  168 ( 389 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),sK3)
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(X2,sK3)
        & m1_pre_topc(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),X3)
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X1,X3)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),X3)
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(sK1,X3)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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

fof(f34,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f33,f32,f31,f30])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1512,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_513,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X0,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_514,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_518,plain,
    ( v2_struct_0(X0)
    | ~ m1_pre_topc(X0,sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_26,c_24])).

cnf(c_519,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0) ),
    inference(renaming,[status(thm)],[c_518])).

cnf(c_1502,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_3256,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK0,sK3,sK3)
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1502])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_534,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_535,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( v2_struct_0(X0)
    | ~ m1_pre_topc(X0,sK0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_26,c_24])).

cnf(c_540,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_1501,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_2186,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3)
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1501])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1744,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_2319,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2186,c_19,c_18,c_1744])).

cnf(c_3271,plain,
    ( k2_tsep_1(sK0,sK3,sK3) = k1_tsep_1(sK0,sK3,sK3)
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3256,c_2319])).

cnf(c_34,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5213,plain,
    ( k2_tsep_1(sK0,sK3,sK3) = k1_tsep_1(sK0,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3271,c_34])).

cnf(c_11,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X3)
    | m1_pre_topc(k2_tsep_1(X3,X0,X1),k2_tsep_1(X3,X2,X4))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_278,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X4,X1)
    | m1_pre_topc(k2_tsep_1(X1,X3,X0),k2_tsep_1(X1,X2,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | sK2 != X0
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_279,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
    | ~ m1_pre_topc(sK2,X2)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_283,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
    | ~ m1_pre_topc(sK2,X2)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_23,c_21])).

cnf(c_284,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK2,X2)
    | ~ m1_pre_topc(sK1,X1)
    | ~ m1_pre_topc(sK1,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_436,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK2,X2)
    | ~ m1_pre_topc(sK1,X1)
    | ~ m1_pre_topc(sK1,X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_25])).

cnf(c_437,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,X1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_441,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(sK1,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0))
    | ~ m1_pre_topc(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_26,c_24,c_22,c_20])).

cnf(c_442,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_1505,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0)) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_5216,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK3,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5213,c_1505])).

cnf(c_35,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18977,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5216,c_34,c_35,c_36,c_37])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_631,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_632,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_636,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_26])).

cnf(c_637,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_636])).

cnf(c_1498,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_5218,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5213,c_1498])).

cnf(c_6631,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5218,c_34,c_35])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(k1_tsep_1(X1,X2,X0))
    | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_656,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X2,X0))
    | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
    | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_657,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0)
    | ~ v1_pre_topc(k1_tsep_1(sK0,X0,X1))
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_661,plain,
    ( v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ v1_pre_topc(k1_tsep_1(sK0,X0,X1))
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_26])).

cnf(c_662,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | ~ v1_pre_topc(k1_tsep_1(sK0,X0,X1))
    | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_661])).

cnf(c_1497,plain,
    ( u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k1_tsep_1(sK0,X0,X1)) = iProver_top
    | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_6649,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK3))
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_pre_topc(k1_tsep_1(sK0,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6631,c_1497])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1517,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1516,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2141,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1517,c_1516])).

cnf(c_6655,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK3)) = u1_struct_0(sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_pre_topc(k1_tsep_1(sK0,sK3,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6649,c_2141])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_581,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_582,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_586,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_26])).

cnf(c_587,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_586])).

cnf(c_1500,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_5217,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5213,c_1500])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_606,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_pre_topc(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_607,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_26])).

cnf(c_612,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_1499,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_5219,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_pre_topc(k1_tsep_1(sK0,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5213,c_1499])).

cnf(c_8709,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6655,c_34,c_35,c_5217,c_5219])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_489,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_490,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_494,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_24])).

cnf(c_495,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_494])).

cnf(c_1503,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_8721,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8709,c_1503])).

cnf(c_11735,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8721,c_34,c_35,c_5218])).

cnf(c_11736,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11735])).

cnf(c_18984,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18977,c_11736])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_469,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,X0)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_470,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_472,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_24])).

cnf(c_473,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_3108,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_7625,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_7626,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7625])).

cnf(c_1793,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_2027,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_2028,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_14,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_33,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_32,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_31,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18984,c_7626,c_2028,c_39,c_35,c_33,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.05/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.05/1.49  
% 7.05/1.49  ------  iProver source info
% 7.05/1.49  
% 7.05/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.05/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.05/1.49  git: non_committed_changes: false
% 7.05/1.49  git: last_make_outside_of_git: false
% 7.05/1.49  
% 7.05/1.49  ------ 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options
% 7.05/1.49  
% 7.05/1.49  --out_options                           all
% 7.05/1.49  --tptp_safe_out                         true
% 7.05/1.49  --problem_path                          ""
% 7.05/1.49  --include_path                          ""
% 7.05/1.49  --clausifier                            res/vclausify_rel
% 7.05/1.49  --clausifier_options                    --mode clausify
% 7.05/1.49  --stdin                                 false
% 7.05/1.49  --stats_out                             all
% 7.05/1.49  
% 7.05/1.49  ------ General Options
% 7.05/1.49  
% 7.05/1.49  --fof                                   false
% 7.05/1.49  --time_out_real                         305.
% 7.05/1.49  --time_out_virtual                      -1.
% 7.05/1.49  --symbol_type_check                     false
% 7.05/1.49  --clausify_out                          false
% 7.05/1.49  --sig_cnt_out                           false
% 7.05/1.49  --trig_cnt_out                          false
% 7.05/1.49  --trig_cnt_out_tolerance                1.
% 7.05/1.49  --trig_cnt_out_sk_spl                   false
% 7.05/1.49  --abstr_cl_out                          false
% 7.05/1.49  
% 7.05/1.49  ------ Global Options
% 7.05/1.49  
% 7.05/1.49  --schedule                              default
% 7.05/1.49  --add_important_lit                     false
% 7.05/1.49  --prop_solver_per_cl                    1000
% 7.05/1.49  --min_unsat_core                        false
% 7.05/1.49  --soft_assumptions                      false
% 7.05/1.49  --soft_lemma_size                       3
% 7.05/1.49  --prop_impl_unit_size                   0
% 7.05/1.49  --prop_impl_unit                        []
% 7.05/1.49  --share_sel_clauses                     true
% 7.05/1.49  --reset_solvers                         false
% 7.05/1.49  --bc_imp_inh                            [conj_cone]
% 7.05/1.49  --conj_cone_tolerance                   3.
% 7.05/1.49  --extra_neg_conj                        none
% 7.05/1.49  --large_theory_mode                     true
% 7.05/1.49  --prolific_symb_bound                   200
% 7.05/1.49  --lt_threshold                          2000
% 7.05/1.49  --clause_weak_htbl                      true
% 7.05/1.49  --gc_record_bc_elim                     false
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing Options
% 7.05/1.49  
% 7.05/1.49  --preprocessing_flag                    true
% 7.05/1.49  --time_out_prep_mult                    0.1
% 7.05/1.49  --splitting_mode                        input
% 7.05/1.49  --splitting_grd                         true
% 7.05/1.49  --splitting_cvd                         false
% 7.05/1.49  --splitting_cvd_svl                     false
% 7.05/1.49  --splitting_nvd                         32
% 7.05/1.49  --sub_typing                            true
% 7.05/1.49  --prep_gs_sim                           true
% 7.05/1.49  --prep_unflatten                        true
% 7.05/1.49  --prep_res_sim                          true
% 7.05/1.49  --prep_upred                            true
% 7.05/1.49  --prep_sem_filter                       exhaustive
% 7.05/1.49  --prep_sem_filter_out                   false
% 7.05/1.49  --pred_elim                             true
% 7.05/1.49  --res_sim_input                         true
% 7.05/1.49  --eq_ax_congr_red                       true
% 7.05/1.49  --pure_diseq_elim                       true
% 7.05/1.49  --brand_transform                       false
% 7.05/1.49  --non_eq_to_eq                          false
% 7.05/1.49  --prep_def_merge                        true
% 7.05/1.49  --prep_def_merge_prop_impl              false
% 7.05/1.49  --prep_def_merge_mbd                    true
% 7.05/1.49  --prep_def_merge_tr_red                 false
% 7.05/1.49  --prep_def_merge_tr_cl                  false
% 7.05/1.49  --smt_preprocessing                     true
% 7.05/1.49  --smt_ac_axioms                         fast
% 7.05/1.49  --preprocessed_out                      false
% 7.05/1.49  --preprocessed_stats                    false
% 7.05/1.49  
% 7.05/1.49  ------ Abstraction refinement Options
% 7.05/1.49  
% 7.05/1.49  --abstr_ref                             []
% 7.05/1.49  --abstr_ref_prep                        false
% 7.05/1.49  --abstr_ref_until_sat                   false
% 7.05/1.49  --abstr_ref_sig_restrict                funpre
% 7.05/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.49  --abstr_ref_under                       []
% 7.05/1.49  
% 7.05/1.49  ------ SAT Options
% 7.05/1.49  
% 7.05/1.49  --sat_mode                              false
% 7.05/1.49  --sat_fm_restart_options                ""
% 7.05/1.49  --sat_gr_def                            false
% 7.05/1.49  --sat_epr_types                         true
% 7.05/1.49  --sat_non_cyclic_types                  false
% 7.05/1.49  --sat_finite_models                     false
% 7.05/1.49  --sat_fm_lemmas                         false
% 7.05/1.49  --sat_fm_prep                           false
% 7.05/1.49  --sat_fm_uc_incr                        true
% 7.05/1.49  --sat_out_model                         small
% 7.05/1.49  --sat_out_clauses                       false
% 7.05/1.49  
% 7.05/1.49  ------ QBF Options
% 7.05/1.49  
% 7.05/1.49  --qbf_mode                              false
% 7.05/1.49  --qbf_elim_univ                         false
% 7.05/1.49  --qbf_dom_inst                          none
% 7.05/1.49  --qbf_dom_pre_inst                      false
% 7.05/1.49  --qbf_sk_in                             false
% 7.05/1.49  --qbf_pred_elim                         true
% 7.05/1.49  --qbf_split                             512
% 7.05/1.49  
% 7.05/1.49  ------ BMC1 Options
% 7.05/1.49  
% 7.05/1.49  --bmc1_incremental                      false
% 7.05/1.49  --bmc1_axioms                           reachable_all
% 7.05/1.49  --bmc1_min_bound                        0
% 7.05/1.49  --bmc1_max_bound                        -1
% 7.05/1.49  --bmc1_max_bound_default                -1
% 7.05/1.49  --bmc1_symbol_reachability              true
% 7.05/1.49  --bmc1_property_lemmas                  false
% 7.05/1.49  --bmc1_k_induction                      false
% 7.05/1.49  --bmc1_non_equiv_states                 false
% 7.05/1.49  --bmc1_deadlock                         false
% 7.05/1.49  --bmc1_ucm                              false
% 7.05/1.49  --bmc1_add_unsat_core                   none
% 7.05/1.49  --bmc1_unsat_core_children              false
% 7.05/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.49  --bmc1_out_stat                         full
% 7.05/1.49  --bmc1_ground_init                      false
% 7.05/1.49  --bmc1_pre_inst_next_state              false
% 7.05/1.49  --bmc1_pre_inst_state                   false
% 7.05/1.49  --bmc1_pre_inst_reach_state             false
% 7.05/1.49  --bmc1_out_unsat_core                   false
% 7.05/1.49  --bmc1_aig_witness_out                  false
% 7.05/1.49  --bmc1_verbose                          false
% 7.05/1.49  --bmc1_dump_clauses_tptp                false
% 7.05/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.49  --bmc1_dump_file                        -
% 7.05/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.49  --bmc1_ucm_extend_mode                  1
% 7.05/1.49  --bmc1_ucm_init_mode                    2
% 7.05/1.49  --bmc1_ucm_cone_mode                    none
% 7.05/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.49  --bmc1_ucm_relax_model                  4
% 7.05/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.49  --bmc1_ucm_layered_model                none
% 7.05/1.49  --bmc1_ucm_max_lemma_size               10
% 7.05/1.49  
% 7.05/1.49  ------ AIG Options
% 7.05/1.49  
% 7.05/1.49  --aig_mode                              false
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation Options
% 7.05/1.49  
% 7.05/1.49  --instantiation_flag                    true
% 7.05/1.49  --inst_sos_flag                         false
% 7.05/1.49  --inst_sos_phase                        true
% 7.05/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel_side                     num_symb
% 7.05/1.49  --inst_solver_per_active                1400
% 7.05/1.49  --inst_solver_calls_frac                1.
% 7.05/1.49  --inst_passive_queue_type               priority_queues
% 7.05/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.49  --inst_passive_queues_freq              [25;2]
% 7.05/1.49  --inst_dismatching                      true
% 7.05/1.49  --inst_eager_unprocessed_to_passive     true
% 7.05/1.49  --inst_prop_sim_given                   true
% 7.05/1.49  --inst_prop_sim_new                     false
% 7.05/1.49  --inst_subs_new                         false
% 7.05/1.49  --inst_eq_res_simp                      false
% 7.05/1.49  --inst_subs_given                       false
% 7.05/1.49  --inst_orphan_elimination               true
% 7.05/1.49  --inst_learning_loop_flag               true
% 7.05/1.49  --inst_learning_start                   3000
% 7.05/1.49  --inst_learning_factor                  2
% 7.05/1.49  --inst_start_prop_sim_after_learn       3
% 7.05/1.49  --inst_sel_renew                        solver
% 7.05/1.49  --inst_lit_activity_flag                true
% 7.05/1.49  --inst_restr_to_given                   false
% 7.05/1.49  --inst_activity_threshold               500
% 7.05/1.49  --inst_out_proof                        true
% 7.05/1.49  
% 7.05/1.49  ------ Resolution Options
% 7.05/1.49  
% 7.05/1.49  --resolution_flag                       true
% 7.05/1.49  --res_lit_sel                           adaptive
% 7.05/1.49  --res_lit_sel_side                      none
% 7.05/1.49  --res_ordering                          kbo
% 7.05/1.49  --res_to_prop_solver                    active
% 7.05/1.49  --res_prop_simpl_new                    false
% 7.05/1.49  --res_prop_simpl_given                  true
% 7.05/1.49  --res_passive_queue_type                priority_queues
% 7.05/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.49  --res_passive_queues_freq               [15;5]
% 7.05/1.49  --res_forward_subs                      full
% 7.05/1.49  --res_backward_subs                     full
% 7.05/1.49  --res_forward_subs_resolution           true
% 7.05/1.49  --res_backward_subs_resolution          true
% 7.05/1.49  --res_orphan_elimination                true
% 7.05/1.49  --res_time_limit                        2.
% 7.05/1.49  --res_out_proof                         true
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Options
% 7.05/1.49  
% 7.05/1.49  --superposition_flag                    true
% 7.05/1.49  --sup_passive_queue_type                priority_queues
% 7.05/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.49  --demod_completeness_check              fast
% 7.05/1.49  --demod_use_ground                      true
% 7.05/1.49  --sup_to_prop_solver                    passive
% 7.05/1.49  --sup_prop_simpl_new                    true
% 7.05/1.49  --sup_prop_simpl_given                  true
% 7.05/1.49  --sup_fun_splitting                     false
% 7.05/1.49  --sup_smt_interval                      50000
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Simplification Setup
% 7.05/1.49  
% 7.05/1.49  --sup_indices_passive                   []
% 7.05/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_full_bw                           [BwDemod]
% 7.05/1.49  --sup_immed_triv                        [TrivRules]
% 7.05/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_immed_bw_main                     []
% 7.05/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  
% 7.05/1.49  ------ Combination Options
% 7.05/1.49  
% 7.05/1.49  --comb_res_mult                         3
% 7.05/1.49  --comb_sup_mult                         2
% 7.05/1.49  --comb_inst_mult                        10
% 7.05/1.49  
% 7.05/1.49  ------ Debug Options
% 7.05/1.49  
% 7.05/1.49  --dbg_backtrace                         false
% 7.05/1.49  --dbg_dump_prop_clauses                 false
% 7.05/1.49  --dbg_dump_prop_clauses_file            -
% 7.05/1.49  --dbg_out_stat                          false
% 7.05/1.49  ------ Parsing...
% 7.05/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.05/1.49  ------ Proving...
% 7.05/1.49  ------ Problem Properties 
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  clauses                                 23
% 7.05/1.49  conjectures                             10
% 7.05/1.49  EPR                                     11
% 7.05/1.49  Horn                                    15
% 7.05/1.49  unary                                   11
% 7.05/1.49  binary                                  1
% 7.05/1.49  lits                                    69
% 7.05/1.49  lits eq                                 7
% 7.05/1.49  fd_pure                                 0
% 7.05/1.49  fd_pseudo                               0
% 7.05/1.49  fd_cond                                 0
% 7.05/1.49  fd_pseudo_cond                          2
% 7.05/1.49  AC symbols                              0
% 7.05/1.49  
% 7.05/1.49  ------ Schedule dynamic 5 is on 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  ------ 
% 7.05/1.49  Current options:
% 7.05/1.49  ------ 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options
% 7.05/1.49  
% 7.05/1.49  --out_options                           all
% 7.05/1.49  --tptp_safe_out                         true
% 7.05/1.49  --problem_path                          ""
% 7.05/1.49  --include_path                          ""
% 7.05/1.49  --clausifier                            res/vclausify_rel
% 7.05/1.49  --clausifier_options                    --mode clausify
% 7.05/1.49  --stdin                                 false
% 7.05/1.49  --stats_out                             all
% 7.05/1.49  
% 7.05/1.49  ------ General Options
% 7.05/1.49  
% 7.05/1.49  --fof                                   false
% 7.05/1.49  --time_out_real                         305.
% 7.05/1.49  --time_out_virtual                      -1.
% 7.05/1.49  --symbol_type_check                     false
% 7.05/1.49  --clausify_out                          false
% 7.05/1.49  --sig_cnt_out                           false
% 7.05/1.49  --trig_cnt_out                          false
% 7.05/1.49  --trig_cnt_out_tolerance                1.
% 7.05/1.49  --trig_cnt_out_sk_spl                   false
% 7.05/1.49  --abstr_cl_out                          false
% 7.05/1.49  
% 7.05/1.49  ------ Global Options
% 7.05/1.49  
% 7.05/1.49  --schedule                              default
% 7.05/1.49  --add_important_lit                     false
% 7.05/1.49  --prop_solver_per_cl                    1000
% 7.05/1.49  --min_unsat_core                        false
% 7.05/1.49  --soft_assumptions                      false
% 7.05/1.49  --soft_lemma_size                       3
% 7.05/1.49  --prop_impl_unit_size                   0
% 7.05/1.49  --prop_impl_unit                        []
% 7.05/1.49  --share_sel_clauses                     true
% 7.05/1.49  --reset_solvers                         false
% 7.05/1.49  --bc_imp_inh                            [conj_cone]
% 7.05/1.49  --conj_cone_tolerance                   3.
% 7.05/1.49  --extra_neg_conj                        none
% 7.05/1.49  --large_theory_mode                     true
% 7.05/1.49  --prolific_symb_bound                   200
% 7.05/1.49  --lt_threshold                          2000
% 7.05/1.49  --clause_weak_htbl                      true
% 7.05/1.49  --gc_record_bc_elim                     false
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing Options
% 7.05/1.49  
% 7.05/1.49  --preprocessing_flag                    true
% 7.05/1.49  --time_out_prep_mult                    0.1
% 7.05/1.49  --splitting_mode                        input
% 7.05/1.49  --splitting_grd                         true
% 7.05/1.49  --splitting_cvd                         false
% 7.05/1.49  --splitting_cvd_svl                     false
% 7.05/1.49  --splitting_nvd                         32
% 7.05/1.49  --sub_typing                            true
% 7.05/1.49  --prep_gs_sim                           true
% 7.05/1.49  --prep_unflatten                        true
% 7.05/1.49  --prep_res_sim                          true
% 7.05/1.49  --prep_upred                            true
% 7.05/1.49  --prep_sem_filter                       exhaustive
% 7.05/1.49  --prep_sem_filter_out                   false
% 7.05/1.49  --pred_elim                             true
% 7.05/1.49  --res_sim_input                         true
% 7.05/1.49  --eq_ax_congr_red                       true
% 7.05/1.49  --pure_diseq_elim                       true
% 7.05/1.49  --brand_transform                       false
% 7.05/1.49  --non_eq_to_eq                          false
% 7.05/1.49  --prep_def_merge                        true
% 7.05/1.49  --prep_def_merge_prop_impl              false
% 7.05/1.49  --prep_def_merge_mbd                    true
% 7.05/1.49  --prep_def_merge_tr_red                 false
% 7.05/1.49  --prep_def_merge_tr_cl                  false
% 7.05/1.49  --smt_preprocessing                     true
% 7.05/1.49  --smt_ac_axioms                         fast
% 7.05/1.49  --preprocessed_out                      false
% 7.05/1.49  --preprocessed_stats                    false
% 7.05/1.49  
% 7.05/1.49  ------ Abstraction refinement Options
% 7.05/1.49  
% 7.05/1.49  --abstr_ref                             []
% 7.05/1.49  --abstr_ref_prep                        false
% 7.05/1.49  --abstr_ref_until_sat                   false
% 7.05/1.49  --abstr_ref_sig_restrict                funpre
% 7.05/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.49  --abstr_ref_under                       []
% 7.05/1.49  
% 7.05/1.49  ------ SAT Options
% 7.05/1.49  
% 7.05/1.49  --sat_mode                              false
% 7.05/1.49  --sat_fm_restart_options                ""
% 7.05/1.49  --sat_gr_def                            false
% 7.05/1.49  --sat_epr_types                         true
% 7.05/1.49  --sat_non_cyclic_types                  false
% 7.05/1.49  --sat_finite_models                     false
% 7.05/1.49  --sat_fm_lemmas                         false
% 7.05/1.49  --sat_fm_prep                           false
% 7.05/1.49  --sat_fm_uc_incr                        true
% 7.05/1.49  --sat_out_model                         small
% 7.05/1.49  --sat_out_clauses                       false
% 7.05/1.49  
% 7.05/1.49  ------ QBF Options
% 7.05/1.49  
% 7.05/1.49  --qbf_mode                              false
% 7.05/1.49  --qbf_elim_univ                         false
% 7.05/1.49  --qbf_dom_inst                          none
% 7.05/1.49  --qbf_dom_pre_inst                      false
% 7.05/1.49  --qbf_sk_in                             false
% 7.05/1.49  --qbf_pred_elim                         true
% 7.05/1.49  --qbf_split                             512
% 7.05/1.49  
% 7.05/1.49  ------ BMC1 Options
% 7.05/1.49  
% 7.05/1.49  --bmc1_incremental                      false
% 7.05/1.49  --bmc1_axioms                           reachable_all
% 7.05/1.49  --bmc1_min_bound                        0
% 7.05/1.49  --bmc1_max_bound                        -1
% 7.05/1.49  --bmc1_max_bound_default                -1
% 7.05/1.49  --bmc1_symbol_reachability              true
% 7.05/1.49  --bmc1_property_lemmas                  false
% 7.05/1.49  --bmc1_k_induction                      false
% 7.05/1.49  --bmc1_non_equiv_states                 false
% 7.05/1.49  --bmc1_deadlock                         false
% 7.05/1.49  --bmc1_ucm                              false
% 7.05/1.49  --bmc1_add_unsat_core                   none
% 7.05/1.49  --bmc1_unsat_core_children              false
% 7.05/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.49  --bmc1_out_stat                         full
% 7.05/1.49  --bmc1_ground_init                      false
% 7.05/1.49  --bmc1_pre_inst_next_state              false
% 7.05/1.49  --bmc1_pre_inst_state                   false
% 7.05/1.49  --bmc1_pre_inst_reach_state             false
% 7.05/1.49  --bmc1_out_unsat_core                   false
% 7.05/1.49  --bmc1_aig_witness_out                  false
% 7.05/1.49  --bmc1_verbose                          false
% 7.05/1.49  --bmc1_dump_clauses_tptp                false
% 7.05/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.49  --bmc1_dump_file                        -
% 7.05/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.49  --bmc1_ucm_extend_mode                  1
% 7.05/1.49  --bmc1_ucm_init_mode                    2
% 7.05/1.49  --bmc1_ucm_cone_mode                    none
% 7.05/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.49  --bmc1_ucm_relax_model                  4
% 7.05/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.49  --bmc1_ucm_layered_model                none
% 7.05/1.49  --bmc1_ucm_max_lemma_size               10
% 7.05/1.49  
% 7.05/1.49  ------ AIG Options
% 7.05/1.49  
% 7.05/1.49  --aig_mode                              false
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation Options
% 7.05/1.49  
% 7.05/1.49  --instantiation_flag                    true
% 7.05/1.49  --inst_sos_flag                         false
% 7.05/1.49  --inst_sos_phase                        true
% 7.05/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel_side                     none
% 7.05/1.49  --inst_solver_per_active                1400
% 7.05/1.49  --inst_solver_calls_frac                1.
% 7.05/1.49  --inst_passive_queue_type               priority_queues
% 7.05/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.49  --inst_passive_queues_freq              [25;2]
% 7.05/1.49  --inst_dismatching                      true
% 7.05/1.49  --inst_eager_unprocessed_to_passive     true
% 7.05/1.49  --inst_prop_sim_given                   true
% 7.05/1.49  --inst_prop_sim_new                     false
% 7.05/1.49  --inst_subs_new                         false
% 7.05/1.49  --inst_eq_res_simp                      false
% 7.05/1.49  --inst_subs_given                       false
% 7.05/1.49  --inst_orphan_elimination               true
% 7.05/1.49  --inst_learning_loop_flag               true
% 7.05/1.49  --inst_learning_start                   3000
% 7.05/1.49  --inst_learning_factor                  2
% 7.05/1.49  --inst_start_prop_sim_after_learn       3
% 7.05/1.49  --inst_sel_renew                        solver
% 7.05/1.49  --inst_lit_activity_flag                true
% 7.05/1.49  --inst_restr_to_given                   false
% 7.05/1.49  --inst_activity_threshold               500
% 7.05/1.49  --inst_out_proof                        true
% 7.05/1.49  
% 7.05/1.49  ------ Resolution Options
% 7.05/1.49  
% 7.05/1.49  --resolution_flag                       false
% 7.05/1.49  --res_lit_sel                           adaptive
% 7.05/1.49  --res_lit_sel_side                      none
% 7.05/1.49  --res_ordering                          kbo
% 7.05/1.49  --res_to_prop_solver                    active
% 7.05/1.49  --res_prop_simpl_new                    false
% 7.05/1.49  --res_prop_simpl_given                  true
% 7.05/1.49  --res_passive_queue_type                priority_queues
% 7.05/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.49  --res_passive_queues_freq               [15;5]
% 7.05/1.49  --res_forward_subs                      full
% 7.05/1.49  --res_backward_subs                     full
% 7.05/1.49  --res_forward_subs_resolution           true
% 7.05/1.49  --res_backward_subs_resolution          true
% 7.05/1.49  --res_orphan_elimination                true
% 7.05/1.49  --res_time_limit                        2.
% 7.05/1.49  --res_out_proof                         true
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Options
% 7.05/1.49  
% 7.05/1.49  --superposition_flag                    true
% 7.05/1.49  --sup_passive_queue_type                priority_queues
% 7.05/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.49  --demod_completeness_check              fast
% 7.05/1.49  --demod_use_ground                      true
% 7.05/1.49  --sup_to_prop_solver                    passive
% 7.05/1.49  --sup_prop_simpl_new                    true
% 7.05/1.49  --sup_prop_simpl_given                  true
% 7.05/1.49  --sup_fun_splitting                     false
% 7.05/1.49  --sup_smt_interval                      50000
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Simplification Setup
% 7.05/1.49  
% 7.05/1.49  --sup_indices_passive                   []
% 7.05/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_full_bw                           [BwDemod]
% 7.05/1.49  --sup_immed_triv                        [TrivRules]
% 7.05/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_immed_bw_main                     []
% 7.05/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  
% 7.05/1.49  ------ Combination Options
% 7.05/1.49  
% 7.05/1.49  --comb_res_mult                         3
% 7.05/1.49  --comb_sup_mult                         2
% 7.05/1.49  --comb_inst_mult                        10
% 7.05/1.49  
% 7.05/1.49  ------ Debug Options
% 7.05/1.49  
% 7.05/1.49  --dbg_backtrace                         false
% 7.05/1.49  --dbg_dump_prop_clauses                 false
% 7.05/1.49  --dbg_dump_prop_clauses_file            -
% 7.05/1.49  --dbg_out_stat                          false
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  ------ Proving...
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  % SZS status Theorem for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  fof(f9,conjecture,(
% 7.05/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f10,negated_conjecture,(
% 7.05/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 7.05/1.49    inference(negated_conjecture,[],[f9])).
% 7.05/1.49  
% 7.05/1.49  fof(f24,plain,(
% 7.05/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f10])).
% 7.05/1.49  
% 7.05/1.49  fof(f25,plain,(
% 7.05/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.05/1.49    inference(flattening,[],[f24])).
% 7.05/1.49  
% 7.05/1.49  fof(f33,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(X0,X1,X2),sK3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK3) & m1_pre_topc(X1,sK3) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f32,plain,(
% 7.05/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,sK2),X3) & ~r1_tsep_1(X1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f31,plain,(
% 7.05/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f30,plain,(
% 7.05/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f34,plain,(
% 7.05/1.49    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.05/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f33,f32,f31,f30])).
% 7.05/1.49  
% 7.05/1.49  fof(f57,plain,(
% 7.05/1.49    m1_pre_topc(sK3,sK0)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f6,axiom,(
% 7.05/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f18,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f6])).
% 7.05/1.49  
% 7.05/1.49  fof(f19,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.05/1.49    inference(flattening,[],[f18])).
% 7.05/1.49  
% 7.05/1.49  fof(f45,plain,(
% 7.05/1.49    ( ! [X0,X1] : (k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f19])).
% 7.05/1.49  
% 7.05/1.49  fof(f50,plain,(
% 7.05/1.49    v2_pre_topc(sK0)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f49,plain,(
% 7.05/1.49    ~v2_struct_0(sK0)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f51,plain,(
% 7.05/1.49    l1_pre_topc(sK0)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f5,axiom,(
% 7.05/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f16,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f5])).
% 7.05/1.49  
% 7.05/1.49  fof(f17,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.05/1.49    inference(flattening,[],[f16])).
% 7.05/1.49  
% 7.05/1.49  fof(f44,plain,(
% 7.05/1.49    ( ! [X0,X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f17])).
% 7.05/1.49  
% 7.05/1.49  fof(f56,plain,(
% 7.05/1.49    ~v2_struct_0(sK3)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f7,axiom,(
% 7.05/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f20,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f7])).
% 7.05/1.49  
% 7.05/1.49  fof(f21,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.05/1.49    inference(flattening,[],[f20])).
% 7.05/1.49  
% 7.05/1.49  fof(f46,plain,(
% 7.05/1.49    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f21])).
% 7.05/1.49  
% 7.05/1.49  fof(f60,plain,(
% 7.05/1.49    ~r1_tsep_1(sK1,sK2)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f52,plain,(
% 7.05/1.49    ~v2_struct_0(sK1)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f54,plain,(
% 7.05/1.49    ~v2_struct_0(sK2)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f53,plain,(
% 7.05/1.49    m1_pre_topc(sK1,sK0)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f55,plain,(
% 7.05/1.49    m1_pre_topc(sK2,sK0)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f58,plain,(
% 7.05/1.49    m1_pre_topc(sK1,sK3)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f59,plain,(
% 7.05/1.49    m1_pre_topc(sK2,sK3)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f4,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f14,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f4])).
% 7.05/1.49  
% 7.05/1.49  fof(f15,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.05/1.49    inference(flattening,[],[f14])).
% 7.05/1.49  
% 7.05/1.49  fof(f43,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f15])).
% 7.05/1.49  
% 7.05/1.49  fof(f3,axiom,(
% 7.05/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f12,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f3])).
% 7.05/1.49  
% 7.05/1.49  fof(f13,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.05/1.49    inference(flattening,[],[f12])).
% 7.05/1.49  
% 7.05/1.49  fof(f28,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.05/1.49    inference(nnf_transformation,[],[f13])).
% 7.05/1.49  
% 7.05/1.49  fof(f39,plain,(
% 7.05/1.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f28])).
% 7.05/1.49  
% 7.05/1.49  fof(f64,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(equality_resolution,[],[f39])).
% 7.05/1.49  
% 7.05/1.49  fof(f1,axiom,(
% 7.05/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f26,plain,(
% 7.05/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.05/1.49    inference(nnf_transformation,[],[f1])).
% 7.05/1.49  
% 7.05/1.49  fof(f27,plain,(
% 7.05/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.05/1.49    inference(flattening,[],[f26])).
% 7.05/1.49  
% 7.05/1.49  fof(f35,plain,(
% 7.05/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.05/1.49    inference(cnf_transformation,[],[f27])).
% 7.05/1.49  
% 7.05/1.49  fof(f63,plain,(
% 7.05/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.05/1.49    inference(equality_resolution,[],[f35])).
% 7.05/1.49  
% 7.05/1.49  fof(f2,axiom,(
% 7.05/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f11,plain,(
% 7.05/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.05/1.49    inference(ennf_transformation,[],[f2])).
% 7.05/1.49  
% 7.05/1.49  fof(f38,plain,(
% 7.05/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f11])).
% 7.05/1.49  
% 7.05/1.49  fof(f41,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f15])).
% 7.05/1.49  
% 7.05/1.49  fof(f42,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f15])).
% 7.05/1.49  
% 7.05/1.49  fof(f8,axiom,(
% 7.05/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f22,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f8])).
% 7.05/1.49  
% 7.05/1.49  fof(f23,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.05/1.49    inference(flattening,[],[f22])).
% 7.05/1.49  
% 7.05/1.49  fof(f29,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.05/1.49    inference(nnf_transformation,[],[f23])).
% 7.05/1.49  
% 7.05/1.49  fof(f48,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f29])).
% 7.05/1.49  
% 7.05/1.49  fof(f47,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f29])).
% 7.05/1.49  
% 7.05/1.49  fof(f61,plain,(
% 7.05/1.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  cnf(c_18,negated_conjecture,
% 7.05/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1512,plain,
% 7.05/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_10,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X0,X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_25,negated_conjecture,
% 7.05/1.49      ( v2_pre_topc(sK0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_513,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X1,X0,X0)
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_514,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ l1_pre_topc(sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(sK0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_513]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_26,negated_conjecture,
% 7.05/1.49      ( ~ v2_struct_0(sK0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_24,negated_conjecture,
% 7.05/1.49      ( l1_pre_topc(sK0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_518,plain,
% 7.05/1.49      ( v2_struct_0(X0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_514,c_26,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_519,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_518]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1502,plain,
% 7.05/1.49      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,X0,X0)
% 7.05/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(X0) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3256,plain,
% 7.05/1.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK0,sK3,sK3)
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1512,c_1502]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_9,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_534,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_535,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ l1_pre_topc(sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(sK0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_534]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_539,plain,
% 7.05/1.49      ( v2_struct_0(X0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_535,c_26,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_540,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_539]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1501,plain,
% 7.05/1.49      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0)
% 7.05/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(X0) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2186,plain,
% 7.05/1.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3)
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1512,c_1501]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_19,negated_conjecture,
% 7.05/1.49      ( ~ v2_struct_0(sK3) ),
% 7.05/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1744,plain,
% 7.05/1.49      ( ~ m1_pre_topc(sK3,sK0)
% 7.05/1.49      | v2_struct_0(sK3)
% 7.05/1.49      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_540]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2319,plain,
% 7.05/1.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK3,sK3) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_2186,c_19,c_18,c_1744]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3271,plain,
% 7.05/1.49      ( k2_tsep_1(sK0,sK3,sK3) = k1_tsep_1(sK0,sK3,sK3)
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.05/1.49      inference(light_normalisation,[status(thm)],[c_3256,c_2319]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_34,plain,
% 7.05/1.49      ( v2_struct_0(sK3) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5213,plain,
% 7.05/1.49      ( k2_tsep_1(sK0,sK3,sK3) = k1_tsep_1(sK0,sK3,sK3) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_3271,c_34]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_11,plain,
% 7.05/1.49      ( r1_tsep_1(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X3)
% 7.05/1.49      | ~ m1_pre_topc(X1,X3)
% 7.05/1.49      | ~ m1_pre_topc(X0,X3)
% 7.05/1.49      | ~ m1_pre_topc(X1,X4)
% 7.05/1.49      | ~ m1_pre_topc(X0,X2)
% 7.05/1.49      | ~ m1_pre_topc(X4,X3)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X3,X0,X1),k2_tsep_1(X3,X2,X4))
% 7.05/1.49      | ~ v2_pre_topc(X3)
% 7.05/1.49      | ~ l1_pre_topc(X3)
% 7.05/1.49      | v2_struct_0(X3)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(X4) ),
% 7.05/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_15,negated_conjecture,
% 7.05/1.49      ( ~ r1_tsep_1(sK1,sK2) ),
% 7.05/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_278,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | ~ m1_pre_topc(X3,X1)
% 7.05/1.49      | ~ m1_pre_topc(X0,X4)
% 7.05/1.49      | ~ m1_pre_topc(X3,X2)
% 7.05/1.49      | ~ m1_pre_topc(X4,X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X1,X3,X0),k2_tsep_1(X1,X2,X4))
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X3)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X4)
% 7.05/1.49      | sK2 != X0
% 7.05/1.49      | sK1 != X3 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_279,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
% 7.05/1.49      | ~ m1_pre_topc(sK2,X2)
% 7.05/1.49      | ~ m1_pre_topc(sK2,X1)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X0)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X1)
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(sK2)
% 7.05/1.49      | v2_struct_0(sK1) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_278]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_23,negated_conjecture,
% 7.05/1.49      ( ~ v2_struct_0(sK1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_21,negated_conjecture,
% 7.05/1.49      ( ~ v2_struct_0(sK2) ),
% 7.05/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_283,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
% 7.05/1.49      | ~ m1_pre_topc(sK2,X2)
% 7.05/1.49      | ~ m1_pre_topc(sK2,X1)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X0)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X1)
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X2) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_279,c_23,c_21]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_284,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
% 7.05/1.49      | ~ m1_pre_topc(sK2,X1)
% 7.05/1.49      | ~ m1_pre_topc(sK2,X2)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X1)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X0)
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_283]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_436,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X1,sK1,sK2),k2_tsep_1(X1,X0,X2))
% 7.05/1.49      | ~ m1_pre_topc(sK2,X1)
% 7.05/1.49      | ~ m1_pre_topc(sK2,X2)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X1)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X0)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_284,c_25]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_437,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0))
% 7.05/1.49      | ~ m1_pre_topc(sK2,X0)
% 7.05/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X1)
% 7.05/1.49      | ~ m1_pre_topc(sK1,sK0)
% 7.05/1.49      | ~ l1_pre_topc(sK0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(sK0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_436]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_22,negated_conjecture,
% 7.05/1.49      ( m1_pre_topc(sK1,sK0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_20,negated_conjecture,
% 7.05/1.49      ( m1_pre_topc(sK2,sK0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_441,plain,
% 7.05/1.49      ( v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X1)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0))
% 7.05/1.49      | ~ m1_pre_topc(sK2,X0) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_437,c_26,c_24,c_22,c_20]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_442,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0))
% 7.05/1.49      | ~ m1_pre_topc(sK2,X0)
% 7.05/1.49      | ~ m1_pre_topc(sK1,X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_441]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1505,plain,
% 7.05/1.49      ( m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(X1,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X1,X0)) = iProver_top
% 7.05/1.49      | m1_pre_topc(sK2,X0) != iProver_top
% 7.05/1.49      | m1_pre_topc(sK1,X1) != iProver_top
% 7.05/1.49      | v2_struct_0(X0) = iProver_top
% 7.05/1.49      | v2_struct_0(X1) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5216,plain,
% 7.05/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK3,sK3)) = iProver_top
% 7.05/1.49      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.05/1.49      | m1_pre_topc(sK1,sK3) != iProver_top
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_5213,c_1505]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_35,plain,
% 7.05/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17,negated_conjecture,
% 7.05/1.49      ( m1_pre_topc(sK1,sK3) ),
% 7.05/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_36,plain,
% 7.05/1.49      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_16,negated_conjecture,
% 7.05/1.49      ( m1_pre_topc(sK2,sK3) ),
% 7.05/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_37,plain,
% 7.05/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_18977,plain,
% 7.05/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK3,sK3)) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_5216,c_34,c_35,c_36,c_37]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_631,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_632,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(sK0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_631]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_636,plain,
% 7.05/1.49      ( v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_632,c_26]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_637,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_636]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1498,plain,
% 7.05/1.49      ( m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(X1,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) = iProver_top
% 7.05/1.49      | v2_struct_0(X0) = iProver_top
% 7.05/1.49      | v2_struct_0(X1) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5218,plain,
% 7.05/1.49      ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) = iProver_top
% 7.05/1.49      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_5213,c_1498]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6631,plain,
% 7.05/1.49      ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_5218,c_34,c_35]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(k1_tsep_1(X1,X2,X0))
% 7.05/1.49      | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
% 7.05/1.49      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)) ),
% 7.05/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_656,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | ~ m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(k1_tsep_1(X1,X2,X0))
% 7.05/1.49      | ~ v1_pre_topc(k1_tsep_1(X1,X2,X0))
% 7.05/1.49      | u1_struct_0(k1_tsep_1(X1,X2,X0)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_657,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 7.05/1.49      | v2_struct_0(sK0)
% 7.05/1.49      | ~ v1_pre_topc(k1_tsep_1(sK0,X0,X1))
% 7.05/1.49      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_656]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_661,plain,
% 7.05/1.49      ( v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ v1_pre_topc(k1_tsep_1(sK0,X0,X1))
% 7.05/1.49      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_657,c_26]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_662,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 7.05/1.49      | ~ v1_pre_topc(k1_tsep_1(sK0,X0,X1))
% 7.05/1.49      | u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_661]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1497,plain,
% 7.05/1.49      ( u1_struct_0(k1_tsep_1(sK0,X0,X1)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 7.05/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(X1,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(X0) = iProver_top
% 7.05/1.49      | v2_struct_0(X1) = iProver_top
% 7.05/1.49      | v2_struct_0(k1_tsep_1(sK0,X0,X1)) = iProver_top
% 7.05/1.49      | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6649,plain,
% 7.05/1.49      ( u1_struct_0(k1_tsep_1(sK0,sK3,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK3))
% 7.05/1.49      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) = iProver_top
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top
% 7.05/1.49      | v1_pre_topc(k1_tsep_1(sK0,sK3,sK3)) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_6631,c_1497]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2,plain,
% 7.05/1.49      ( r1_tarski(X0,X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1517,plain,
% 7.05/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3,plain,
% 7.05/1.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.05/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1516,plain,
% 7.05/1.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2141,plain,
% 7.05/1.49      ( k2_xboole_0(X0,X0) = X0 ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1517,c_1516]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6655,plain,
% 7.05/1.49      ( u1_struct_0(k1_tsep_1(sK0,sK3,sK3)) = u1_struct_0(sK3)
% 7.05/1.49      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) = iProver_top
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top
% 7.05/1.49      | v1_pre_topc(k1_tsep_1(sK0,sK3,sK3)) != iProver_top ),
% 7.05/1.49      inference(demodulation,[status(thm)],[c_6649,c_2141]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
% 7.05/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_581,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_582,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 7.05/1.49      | v2_struct_0(sK0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_581]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_586,plain,
% 7.05/1.49      ( ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_582,c_26]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_587,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_586]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1500,plain,
% 7.05/1.49      ( m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(X1,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(X0) = iProver_top
% 7.05/1.49      | v2_struct_0(X1) = iProver_top
% 7.05/1.49      | v2_struct_0(k2_tsep_1(sK0,X0,X1)) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5217,plain,
% 7.05/1.49      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) != iProver_top
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_5213,c_1500]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v1_pre_topc(k2_tsep_1(X1,X2,X0)) ),
% 7.05/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_606,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X2)
% 7.05/1.49      | v1_pre_topc(k2_tsep_1(X1,X2,X0))
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_607,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(sK0)
% 7.05/1.49      | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_606]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_611,plain,
% 7.05/1.49      ( v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_607,c_26]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_612,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | v2_struct_0(X0)
% 7.05/1.49      | v2_struct_0(X1)
% 7.05/1.49      | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_611]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1499,plain,
% 7.05/1.49      ( m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(X1,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(X0) = iProver_top
% 7.05/1.49      | v2_struct_0(X1) = iProver_top
% 7.05/1.49      | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5219,plain,
% 7.05/1.49      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.05/1.49      | v2_struct_0(sK3) = iProver_top
% 7.05/1.49      | v1_pre_topc(k1_tsep_1(sK0,sK3,sK3)) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_5213,c_1499]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8709,plain,
% 7.05/1.49      ( u1_struct_0(k1_tsep_1(sK0,sK3,sK3)) = u1_struct_0(sK3) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_6655,c_34,c_35,c_5217,c_5219]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_12,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X0)
% 7.05/1.49      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_489,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X1,X2)
% 7.05/1.49      | ~ m1_pre_topc(X0,X2)
% 7.05/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.05/1.49      | ~ l1_pre_topc(X2)
% 7.05/1.49      | sK0 != X2 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_490,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.05/1.49      | ~ l1_pre_topc(sK0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_489]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_494,plain,
% 7.05/1.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X0,X1) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_490,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_495,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_494]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1503,plain,
% 7.05/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.05/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(X1,sK0) != iProver_top
% 7.05/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8721,plain,
% 7.05/1.49      ( m1_pre_topc(X0,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
% 7.05/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) != iProver_top
% 7.05/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_8709,c_1503]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_11735,plain,
% 7.05/1.49      ( m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | m1_pre_topc(X0,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
% 7.05/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_8721,c_34,c_35,c_5218]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_11736,plain,
% 7.05/1.49      ( m1_pre_topc(X0,k1_tsep_1(sK0,sK3,sK3)) != iProver_top
% 7.05/1.49      | m1_pre_topc(X0,sK0) != iProver_top
% 7.05/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_11735]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_18984,plain,
% 7.05/1.49      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 7.05/1.49      | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_18977,c_11736]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_13,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(X2,X0)
% 7.05/1.49      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 7.05/1.49      | ~ v2_pre_topc(X1)
% 7.05/1.49      | ~ l1_pre_topc(X1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_469,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X2,X1)
% 7.05/1.49      | m1_pre_topc(X2,X0)
% 7.05/1.49      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 7.05/1.49      | ~ l1_pre_topc(X1)
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_470,plain,
% 7.05/1.49      ( m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.05/1.49      | ~ l1_pre_topc(sK0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_469]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_472,plain,
% 7.05/1.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | m1_pre_topc(X0,X1) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_470,c_24]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_473,plain,
% 7.05/1.49      ( m1_pre_topc(X0,X1)
% 7.05/1.49      | ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | ~ m1_pre_topc(X1,sK0)
% 7.05/1.49      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_472]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3108,plain,
% 7.05/1.49      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.49      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
% 7.05/1.49      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 7.05/1.49      | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_473]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_7625,plain,
% 7.05/1.50      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
% 7.05/1.50      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 7.05/1.50      | ~ m1_pre_topc(sK3,sK0)
% 7.05/1.50      | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
% 7.05/1.50      inference(instantiation,[status(thm)],[c_3108]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_7626,plain,
% 7.05/1.50      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) = iProver_top
% 7.05/1.50      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 7.05/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.05/1.50      | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) != iProver_top ),
% 7.05/1.50      inference(predicate_to_equality,[status(thm)],[c_7625]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_1793,plain,
% 7.05/1.50      ( ~ m1_pre_topc(X0,sK0)
% 7.05/1.50      | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
% 7.05/1.50      | ~ m1_pre_topc(sK1,sK0)
% 7.05/1.50      | v2_struct_0(X0)
% 7.05/1.50      | v2_struct_0(sK1) ),
% 7.05/1.50      inference(instantiation,[status(thm)],[c_637]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_2027,plain,
% 7.05/1.50      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 7.05/1.50      | ~ m1_pre_topc(sK2,sK0)
% 7.05/1.50      | ~ m1_pre_topc(sK1,sK0)
% 7.05/1.50      | v2_struct_0(sK2)
% 7.05/1.50      | v2_struct_0(sK1) ),
% 7.05/1.50      inference(instantiation,[status(thm)],[c_1793]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_2028,plain,
% 7.05/1.50      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
% 7.05/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.05/1.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 7.05/1.50      | v2_struct_0(sK2) = iProver_top
% 7.05/1.50      | v2_struct_0(sK1) = iProver_top ),
% 7.05/1.50      inference(predicate_to_equality,[status(thm)],[c_2027]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_14,negated_conjecture,
% 7.05/1.50      ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
% 7.05/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_39,plain,
% 7.05/1.50      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) != iProver_top ),
% 7.05/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_33,plain,
% 7.05/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.05/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_32,plain,
% 7.05/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 7.05/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_31,plain,
% 7.05/1.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 7.05/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(c_30,plain,
% 7.05/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 7.05/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.05/1.50  
% 7.05/1.50  cnf(contradiction,plain,
% 7.05/1.50      ( $false ),
% 7.05/1.50      inference(minisat,
% 7.05/1.50                [status(thm)],
% 7.05/1.50                [c_18984,c_7626,c_2028,c_39,c_35,c_33,c_32,c_31,c_30]) ).
% 7.05/1.50  
% 7.05/1.50  
% 7.05/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.05/1.50  
% 7.05/1.50  ------                               Statistics
% 7.05/1.50  
% 7.05/1.50  ------ General
% 7.05/1.50  
% 7.05/1.50  abstr_ref_over_cycles:                  0
% 7.05/1.50  abstr_ref_under_cycles:                 0
% 7.05/1.50  gc_basic_clause_elim:                   0
% 7.05/1.50  forced_gc_time:                         0
% 7.05/1.50  parsing_time:                           0.011
% 7.05/1.50  unif_index_cands_time:                  0.
% 7.05/1.50  unif_index_add_time:                    0.
% 7.05/1.50  orderings_time:                         0.
% 7.05/1.50  out_proof_time:                         0.014
% 7.05/1.50  total_time:                             0.622
% 7.05/1.50  num_of_symbols:                         48
% 7.05/1.50  num_of_terms:                           33115
% 7.05/1.50  
% 7.05/1.50  ------ Preprocessing
% 7.05/1.50  
% 7.05/1.50  num_of_splits:                          0
% 7.05/1.50  num_of_split_atoms:                     0
% 7.05/1.50  num_of_reused_defs:                     0
% 7.05/1.50  num_eq_ax_congr_red:                    10
% 7.05/1.50  num_of_sem_filtered_clauses:            1
% 7.05/1.50  num_of_subtypes:                        0
% 7.05/1.50  monotx_restored_types:                  0
% 7.05/1.50  sat_num_of_epr_types:                   0
% 7.05/1.50  sat_num_of_non_cyclic_types:            0
% 7.05/1.50  sat_guarded_non_collapsed_types:        0
% 7.05/1.50  num_pure_diseq_elim:                    0
% 7.05/1.50  simp_replaced_by:                       0
% 7.05/1.50  res_preprocessed:                       118
% 7.05/1.50  prep_upred:                             0
% 7.05/1.50  prep_unflattend:                        15
% 7.05/1.50  smt_new_axioms:                         0
% 7.05/1.50  pred_elim_cands:                        4
% 7.05/1.50  pred_elim:                              3
% 7.05/1.50  pred_elim_cl:                           3
% 7.05/1.50  pred_elim_cycles:                       6
% 7.05/1.50  merged_defs:                            0
% 7.05/1.50  merged_defs_ncl:                        0
% 7.05/1.50  bin_hyper_res:                          0
% 7.05/1.50  prep_cycles:                            4
% 7.05/1.50  pred_elim_time:                         0.02
% 7.05/1.50  splitting_time:                         0.
% 7.05/1.50  sem_filter_time:                        0.
% 7.05/1.50  monotx_time:                            0.001
% 7.05/1.50  subtype_inf_time:                       0.
% 7.05/1.50  
% 7.05/1.50  ------ Problem properties
% 7.05/1.50  
% 7.05/1.50  clauses:                                23
% 7.05/1.50  conjectures:                            10
% 7.05/1.50  epr:                                    11
% 7.05/1.50  horn:                                   15
% 7.05/1.50  ground:                                 10
% 7.05/1.50  unary:                                  11
% 7.05/1.50  binary:                                 1
% 7.05/1.50  lits:                                   69
% 7.05/1.50  lits_eq:                                7
% 7.05/1.50  fd_pure:                                0
% 7.05/1.50  fd_pseudo:                              0
% 7.05/1.50  fd_cond:                                0
% 7.05/1.50  fd_pseudo_cond:                         2
% 7.05/1.50  ac_symbols:                             0
% 7.05/1.50  
% 7.05/1.50  ------ Propositional Solver
% 7.05/1.50  
% 7.05/1.50  prop_solver_calls:                      29
% 7.05/1.50  prop_fast_solver_calls:                 1732
% 7.05/1.50  smt_solver_calls:                       0
% 7.05/1.50  smt_fast_solver_calls:                  0
% 7.05/1.50  prop_num_of_clauses:                    5452
% 7.05/1.50  prop_preprocess_simplified:             11163
% 7.05/1.50  prop_fo_subsumed:                       193
% 7.05/1.50  prop_solver_time:                       0.
% 7.05/1.50  smt_solver_time:                        0.
% 7.05/1.50  smt_fast_solver_time:                   0.
% 7.05/1.50  prop_fast_solver_time:                  0.
% 7.05/1.50  prop_unsat_core_time:                   0.
% 7.05/1.50  
% 7.05/1.50  ------ QBF
% 7.05/1.50  
% 7.05/1.50  qbf_q_res:                              0
% 7.05/1.50  qbf_num_tautologies:                    0
% 7.05/1.50  qbf_prep_cycles:                        0
% 7.05/1.50  
% 7.05/1.50  ------ BMC1
% 7.05/1.50  
% 7.05/1.50  bmc1_current_bound:                     -1
% 7.05/1.50  bmc1_last_solved_bound:                 -1
% 7.05/1.50  bmc1_unsat_core_size:                   -1
% 7.05/1.50  bmc1_unsat_core_parents_size:           -1
% 7.05/1.50  bmc1_merge_next_fun:                    0
% 7.05/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.05/1.50  
% 7.05/1.50  ------ Instantiation
% 7.05/1.50  
% 7.05/1.50  inst_num_of_clauses:                    1628
% 7.05/1.50  inst_num_in_passive:                    536
% 7.05/1.50  inst_num_in_active:                     738
% 7.05/1.50  inst_num_in_unprocessed:                354
% 7.05/1.50  inst_num_of_loops:                      780
% 7.05/1.50  inst_num_of_learning_restarts:          0
% 7.05/1.50  inst_num_moves_active_passive:          40
% 7.05/1.50  inst_lit_activity:                      0
% 7.05/1.50  inst_lit_activity_moves:                1
% 7.05/1.50  inst_num_tautologies:                   0
% 7.05/1.50  inst_num_prop_implied:                  0
% 7.05/1.50  inst_num_existing_simplified:           0
% 7.05/1.50  inst_num_eq_res_simplified:             0
% 7.05/1.50  inst_num_child_elim:                    0
% 7.05/1.50  inst_num_of_dismatching_blockings:      4282
% 7.05/1.50  inst_num_of_non_proper_insts:           1501
% 7.05/1.50  inst_num_of_duplicates:                 0
% 7.05/1.50  inst_inst_num_from_inst_to_res:         0
% 7.05/1.50  inst_dismatching_checking_time:         0.
% 7.05/1.50  
% 7.05/1.50  ------ Resolution
% 7.05/1.50  
% 7.05/1.50  res_num_of_clauses:                     0
% 7.05/1.50  res_num_in_passive:                     0
% 7.05/1.50  res_num_in_active:                      0
% 7.05/1.50  res_num_of_loops:                       122
% 7.05/1.50  res_forward_subset_subsumed:            24
% 7.05/1.50  res_backward_subset_subsumed:           0
% 7.05/1.50  res_forward_subsumed:                   0
% 7.05/1.50  res_backward_subsumed:                  0
% 7.05/1.50  res_forward_subsumption_resolution:     5
% 7.05/1.50  res_backward_subsumption_resolution:    0
% 7.05/1.50  res_clause_to_clause_subsumption:       1777
% 7.05/1.50  res_orphan_elimination:                 0
% 7.05/1.50  res_tautology_del:                      23
% 7.05/1.50  res_num_eq_res_simplified:              0
% 7.05/1.50  res_num_sel_changes:                    0
% 7.05/1.50  res_moves_from_active_to_pass:          0
% 7.05/1.50  
% 7.05/1.50  ------ Superposition
% 7.05/1.50  
% 7.05/1.50  sup_time_total:                         0.
% 7.05/1.50  sup_time_generating:                    0.
% 7.05/1.50  sup_time_sim_full:                      0.
% 7.05/1.50  sup_time_sim_immed:                     0.
% 7.05/1.50  
% 7.05/1.50  sup_num_of_clauses:                     371
% 7.05/1.50  sup_num_in_active:                      142
% 7.05/1.50  sup_num_in_passive:                     229
% 7.05/1.50  sup_num_of_loops:                       154
% 7.05/1.50  sup_fw_superposition:                   163
% 7.05/1.50  sup_bw_superposition:                   329
% 7.05/1.50  sup_immediate_simplified:               166
% 7.05/1.50  sup_given_eliminated:                   0
% 7.05/1.50  comparisons_done:                       0
% 7.05/1.50  comparisons_avoided:                    0
% 7.05/1.50  
% 7.05/1.50  ------ Simplifications
% 7.05/1.50  
% 7.05/1.50  
% 7.05/1.50  sim_fw_subset_subsumed:                 9
% 7.05/1.50  sim_bw_subset_subsumed:                 9
% 7.05/1.50  sim_fw_subsumed:                        20
% 7.05/1.50  sim_bw_subsumed:                        0
% 7.05/1.50  sim_fw_subsumption_res:                 10
% 7.05/1.50  sim_bw_subsumption_res:                 0
% 7.05/1.50  sim_tautology_del:                      61
% 7.05/1.50  sim_eq_tautology_del:                   27
% 7.05/1.50  sim_eq_res_simp:                        0
% 7.05/1.50  sim_fw_demodulated:                     36
% 7.05/1.50  sim_bw_demodulated:                     13
% 7.05/1.50  sim_light_normalised:                   121
% 7.05/1.50  sim_joinable_taut:                      0
% 7.05/1.50  sim_joinable_simp:                      0
% 7.05/1.50  sim_ac_normalised:                      0
% 7.05/1.50  sim_smt_subsumption:                    0
% 7.05/1.50  
%------------------------------------------------------------------------------
