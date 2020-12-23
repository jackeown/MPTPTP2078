%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:53 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :  189 (4174 expanded)
%              Number of clauses        :  120 (1164 expanded)
%              Number of leaves         :   17 (1349 expanded)
%              Depth                    :   20
%              Number of atoms          :  660 (35338 expanded)
%              Number of equality atoms :  168 (1371 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(X2,X0)
                | ~ v3_pre_topc(X2,X0) )
              & v6_tops_1(X2,X0) )
            | ( ~ v6_tops_1(X3,X1)
              & v4_tops_1(X3,X1)
              & v3_pre_topc(X3,X1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ( ( ~ v4_tops_1(X2,X0)
              | ~ v3_pre_topc(X2,X0) )
            & v6_tops_1(X2,X0) )
          | ( ~ v6_tops_1(sK3,X1)
            & v4_tops_1(sK3,X1)
            & v3_pre_topc(sK3,X1) ) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,X0)
                    | ~ v3_pre_topc(X2,X0) )
                  & v6_tops_1(X2,X0) )
                | ( ~ v6_tops_1(X3,X1)
                  & v4_tops_1(X3,X1)
                  & v3_pre_topc(X3,X1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(sK2,X0)
                  | ~ v3_pre_topc(sK2,X0) )
                & v6_tops_1(sK2,X0) )
              | ( ~ v6_tops_1(X3,X1)
                & v4_tops_1(X3,X1)
                & v3_pre_topc(X3,X1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,X0)
                      | ~ v3_pre_topc(X2,X0) )
                    & v6_tops_1(X2,X0) )
                  | ( ~ v6_tops_1(X3,sK1)
                    & v4_tops_1(X3,sK1)
                    & v3_pre_topc(X3,sK1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f46,f45,f44,f43])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1561,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1570,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_753,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_754,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_1537,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2800,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1537])).

cnf(c_9004,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0))))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_2800])).

cnf(c_24657,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(superposition,[status(thm)],[c_1561,c_9004])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1569,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2243,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1561,c_1569])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_391,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X2 != X1
    | X3 != X0
    | k2_pre_topc(X3,X2) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_8])).

cnf(c_392,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_456,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k2_pre_topc(X0,X1) = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_30])).

cnf(c_457,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_1557,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_4691,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2)
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2243,c_1557])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_30])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_1866,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_1867,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1866])).

cnf(c_1929,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1930,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_2199,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2200,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2199])).

cnf(c_1535,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_2244,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1569])).

cnf(c_4099,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_1561,c_2244])).

cnf(c_16,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_344,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_345,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_30])).

cnf(c_350,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_349])).

cnf(c_1560,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_2747,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1560])).

cnf(c_4127,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4099,c_2747])).

cnf(c_14,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_675,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_676,plain,
    ( ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_1542,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
    | v6_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_3545,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1561,c_1542])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( ~ v6_tops_1(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( v6_tops_1(sK3,sK1) != iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_29])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_1860,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_1861,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_1875,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_1876,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1875])).

cnf(c_13,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_531,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_532,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_1900,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_1901,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
    | v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1900])).

cnf(c_1903,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1904,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2263,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2264,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2263])).

cnf(c_12,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_546,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_547,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_2274,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_2275,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_483,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_484,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_2292,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_2723,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2292])).

cnf(c_2724,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2723])).

cnf(c_3611,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3545,c_35,c_36,c_37,c_38,c_39,c_1861,c_1876,c_1901,c_1904,c_2264,c_2275,c_2724])).

cnf(c_4130,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4127,c_3611])).

cnf(c_23742,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4691,c_35,c_1867,c_1930,c_2200,c_4130])).

cnf(c_24693,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_24657,c_2243,c_23742])).

cnf(c_10,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_735,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_736,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_1538,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_3626,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3611,c_1538])).

cnf(c_2749,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1560])).

cnf(c_7045,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3611,c_2749])).

cnf(c_7058,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7045,c_35,c_1867,c_2200,c_4130])).

cnf(c_22,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1567,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7063,plain,
    ( v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7058,c_1567])).

cnf(c_21,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v6_tops_1(sK3,sK1) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1566,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7064,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7058,c_1566])).

cnf(c_7176,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7063,c_35,c_36,c_42,c_1861,c_1867,c_1876,c_1901,c_2200,c_2264,c_2275,c_2724,c_4130,c_7064])).

cnf(c_16365,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3626,c_35,c_36,c_42,c_1861,c_1867,c_1876,c_1901,c_2200,c_2264,c_2275,c_2724,c_4130,c_7063,c_7064])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1571,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_16371,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16365,c_1571])).

cnf(c_26833,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24693,c_16371])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_1884,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_1885,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26833,c_1885,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.40/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/1.51  
% 7.40/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.40/1.51  
% 7.40/1.51  ------  iProver source info
% 7.40/1.51  
% 7.40/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.40/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.40/1.51  git: non_committed_changes: false
% 7.40/1.51  git: last_make_outside_of_git: false
% 7.40/1.51  
% 7.40/1.51  ------ 
% 7.40/1.51  
% 7.40/1.51  ------ Input Options
% 7.40/1.51  
% 7.40/1.51  --out_options                           all
% 7.40/1.51  --tptp_safe_out                         true
% 7.40/1.51  --problem_path                          ""
% 7.40/1.51  --include_path                          ""
% 7.40/1.51  --clausifier                            res/vclausify_rel
% 7.40/1.51  --clausifier_options                    --mode clausify
% 7.40/1.51  --stdin                                 false
% 7.40/1.51  --stats_out                             all
% 7.40/1.51  
% 7.40/1.51  ------ General Options
% 7.40/1.51  
% 7.40/1.51  --fof                                   false
% 7.40/1.51  --time_out_real                         305.
% 7.40/1.51  --time_out_virtual                      -1.
% 7.40/1.51  --symbol_type_check                     false
% 7.40/1.51  --clausify_out                          false
% 7.40/1.51  --sig_cnt_out                           false
% 7.40/1.51  --trig_cnt_out                          false
% 7.40/1.51  --trig_cnt_out_tolerance                1.
% 7.40/1.51  --trig_cnt_out_sk_spl                   false
% 7.40/1.51  --abstr_cl_out                          false
% 7.40/1.51  
% 7.40/1.51  ------ Global Options
% 7.40/1.51  
% 7.40/1.51  --schedule                              default
% 7.40/1.51  --add_important_lit                     false
% 7.40/1.51  --prop_solver_per_cl                    1000
% 7.40/1.51  --min_unsat_core                        false
% 7.40/1.51  --soft_assumptions                      false
% 7.40/1.51  --soft_lemma_size                       3
% 7.40/1.51  --prop_impl_unit_size                   0
% 7.40/1.51  --prop_impl_unit                        []
% 7.40/1.51  --share_sel_clauses                     true
% 7.40/1.51  --reset_solvers                         false
% 7.40/1.51  --bc_imp_inh                            [conj_cone]
% 7.40/1.51  --conj_cone_tolerance                   3.
% 7.40/1.51  --extra_neg_conj                        none
% 7.40/1.51  --large_theory_mode                     true
% 7.40/1.51  --prolific_symb_bound                   200
% 7.40/1.51  --lt_threshold                          2000
% 7.40/1.51  --clause_weak_htbl                      true
% 7.40/1.51  --gc_record_bc_elim                     false
% 7.40/1.51  
% 7.40/1.51  ------ Preprocessing Options
% 7.40/1.51  
% 7.40/1.51  --preprocessing_flag                    true
% 7.40/1.51  --time_out_prep_mult                    0.1
% 7.40/1.51  --splitting_mode                        input
% 7.40/1.51  --splitting_grd                         true
% 7.40/1.51  --splitting_cvd                         false
% 7.40/1.51  --splitting_cvd_svl                     false
% 7.40/1.51  --splitting_nvd                         32
% 7.40/1.51  --sub_typing                            true
% 7.40/1.51  --prep_gs_sim                           true
% 7.40/1.51  --prep_unflatten                        true
% 7.40/1.51  --prep_res_sim                          true
% 7.40/1.51  --prep_upred                            true
% 7.40/1.51  --prep_sem_filter                       exhaustive
% 7.40/1.51  --prep_sem_filter_out                   false
% 7.40/1.51  --pred_elim                             true
% 7.40/1.51  --res_sim_input                         true
% 7.40/1.51  --eq_ax_congr_red                       true
% 7.40/1.51  --pure_diseq_elim                       true
% 7.40/1.51  --brand_transform                       false
% 7.40/1.51  --non_eq_to_eq                          false
% 7.40/1.51  --prep_def_merge                        true
% 7.40/1.51  --prep_def_merge_prop_impl              false
% 7.40/1.51  --prep_def_merge_mbd                    true
% 7.40/1.51  --prep_def_merge_tr_red                 false
% 7.40/1.51  --prep_def_merge_tr_cl                  false
% 7.40/1.51  --smt_preprocessing                     true
% 7.40/1.51  --smt_ac_axioms                         fast
% 7.40/1.51  --preprocessed_out                      false
% 7.40/1.51  --preprocessed_stats                    false
% 7.40/1.51  
% 7.40/1.51  ------ Abstraction refinement Options
% 7.40/1.51  
% 7.40/1.51  --abstr_ref                             []
% 7.40/1.51  --abstr_ref_prep                        false
% 7.40/1.51  --abstr_ref_until_sat                   false
% 7.40/1.51  --abstr_ref_sig_restrict                funpre
% 7.40/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.40/1.51  --abstr_ref_under                       []
% 7.40/1.51  
% 7.40/1.51  ------ SAT Options
% 7.40/1.51  
% 7.40/1.51  --sat_mode                              false
% 7.40/1.51  --sat_fm_restart_options                ""
% 7.40/1.51  --sat_gr_def                            false
% 7.40/1.51  --sat_epr_types                         true
% 7.40/1.51  --sat_non_cyclic_types                  false
% 7.40/1.51  --sat_finite_models                     false
% 7.40/1.51  --sat_fm_lemmas                         false
% 7.40/1.51  --sat_fm_prep                           false
% 7.40/1.51  --sat_fm_uc_incr                        true
% 7.40/1.51  --sat_out_model                         small
% 7.40/1.51  --sat_out_clauses                       false
% 7.40/1.51  
% 7.40/1.51  ------ QBF Options
% 7.40/1.51  
% 7.40/1.51  --qbf_mode                              false
% 7.40/1.51  --qbf_elim_univ                         false
% 7.40/1.51  --qbf_dom_inst                          none
% 7.40/1.51  --qbf_dom_pre_inst                      false
% 7.40/1.51  --qbf_sk_in                             false
% 7.40/1.51  --qbf_pred_elim                         true
% 7.40/1.51  --qbf_split                             512
% 7.40/1.51  
% 7.40/1.51  ------ BMC1 Options
% 7.40/1.51  
% 7.40/1.51  --bmc1_incremental                      false
% 7.40/1.51  --bmc1_axioms                           reachable_all
% 7.40/1.51  --bmc1_min_bound                        0
% 7.40/1.51  --bmc1_max_bound                        -1
% 7.40/1.51  --bmc1_max_bound_default                -1
% 7.40/1.51  --bmc1_symbol_reachability              true
% 7.40/1.51  --bmc1_property_lemmas                  false
% 7.40/1.51  --bmc1_k_induction                      false
% 7.40/1.51  --bmc1_non_equiv_states                 false
% 7.40/1.51  --bmc1_deadlock                         false
% 7.40/1.51  --bmc1_ucm                              false
% 7.40/1.51  --bmc1_add_unsat_core                   none
% 7.40/1.52  --bmc1_unsat_core_children              false
% 7.40/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.40/1.52  --bmc1_out_stat                         full
% 7.40/1.52  --bmc1_ground_init                      false
% 7.40/1.52  --bmc1_pre_inst_next_state              false
% 7.40/1.52  --bmc1_pre_inst_state                   false
% 7.40/1.52  --bmc1_pre_inst_reach_state             false
% 7.40/1.52  --bmc1_out_unsat_core                   false
% 7.40/1.52  --bmc1_aig_witness_out                  false
% 7.40/1.52  --bmc1_verbose                          false
% 7.40/1.52  --bmc1_dump_clauses_tptp                false
% 7.40/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.40/1.52  --bmc1_dump_file                        -
% 7.40/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.40/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.40/1.52  --bmc1_ucm_extend_mode                  1
% 7.40/1.52  --bmc1_ucm_init_mode                    2
% 7.40/1.52  --bmc1_ucm_cone_mode                    none
% 7.40/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.40/1.52  --bmc1_ucm_relax_model                  4
% 7.40/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.40/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.40/1.52  --bmc1_ucm_layered_model                none
% 7.40/1.52  --bmc1_ucm_max_lemma_size               10
% 7.40/1.52  
% 7.40/1.52  ------ AIG Options
% 7.40/1.52  
% 7.40/1.52  --aig_mode                              false
% 7.40/1.52  
% 7.40/1.52  ------ Instantiation Options
% 7.40/1.52  
% 7.40/1.52  --instantiation_flag                    true
% 7.40/1.52  --inst_sos_flag                         false
% 7.40/1.52  --inst_sos_phase                        true
% 7.40/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.40/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.40/1.52  --inst_lit_sel_side                     num_symb
% 7.40/1.52  --inst_solver_per_active                1400
% 7.40/1.52  --inst_solver_calls_frac                1.
% 7.40/1.52  --inst_passive_queue_type               priority_queues
% 7.40/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.40/1.52  --inst_passive_queues_freq              [25;2]
% 7.40/1.52  --inst_dismatching                      true
% 7.40/1.52  --inst_eager_unprocessed_to_passive     true
% 7.40/1.52  --inst_prop_sim_given                   true
% 7.40/1.52  --inst_prop_sim_new                     false
% 7.40/1.52  --inst_subs_new                         false
% 7.40/1.52  --inst_eq_res_simp                      false
% 7.40/1.52  --inst_subs_given                       false
% 7.40/1.52  --inst_orphan_elimination               true
% 7.40/1.52  --inst_learning_loop_flag               true
% 7.40/1.52  --inst_learning_start                   3000
% 7.40/1.52  --inst_learning_factor                  2
% 7.40/1.52  --inst_start_prop_sim_after_learn       3
% 7.40/1.52  --inst_sel_renew                        solver
% 7.40/1.52  --inst_lit_activity_flag                true
% 7.40/1.52  --inst_restr_to_given                   false
% 7.40/1.52  --inst_activity_threshold               500
% 7.40/1.52  --inst_out_proof                        true
% 7.40/1.52  
% 7.40/1.52  ------ Resolution Options
% 7.40/1.52  
% 7.40/1.52  --resolution_flag                       true
% 7.40/1.52  --res_lit_sel                           adaptive
% 7.40/1.52  --res_lit_sel_side                      none
% 7.40/1.52  --res_ordering                          kbo
% 7.40/1.52  --res_to_prop_solver                    active
% 7.40/1.52  --res_prop_simpl_new                    false
% 7.40/1.52  --res_prop_simpl_given                  true
% 7.40/1.52  --res_passive_queue_type                priority_queues
% 7.40/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.40/1.52  --res_passive_queues_freq               [15;5]
% 7.40/1.52  --res_forward_subs                      full
% 7.40/1.52  --res_backward_subs                     full
% 7.40/1.52  --res_forward_subs_resolution           true
% 7.40/1.52  --res_backward_subs_resolution          true
% 7.40/1.52  --res_orphan_elimination                true
% 7.40/1.52  --res_time_limit                        2.
% 7.40/1.52  --res_out_proof                         true
% 7.40/1.52  
% 7.40/1.52  ------ Superposition Options
% 7.40/1.52  
% 7.40/1.52  --superposition_flag                    true
% 7.40/1.52  --sup_passive_queue_type                priority_queues
% 7.40/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.40/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.40/1.52  --demod_completeness_check              fast
% 7.40/1.52  --demod_use_ground                      true
% 7.40/1.52  --sup_to_prop_solver                    passive
% 7.40/1.52  --sup_prop_simpl_new                    true
% 7.40/1.52  --sup_prop_simpl_given                  true
% 7.40/1.52  --sup_fun_splitting                     false
% 7.40/1.52  --sup_smt_interval                      50000
% 7.40/1.52  
% 7.40/1.52  ------ Superposition Simplification Setup
% 7.40/1.52  
% 7.40/1.52  --sup_indices_passive                   []
% 7.40/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.40/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.40/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.40/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.40/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.40/1.52  --sup_full_bw                           [BwDemod]
% 7.40/1.52  --sup_immed_triv                        [TrivRules]
% 7.40/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.40/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.40/1.52  --sup_immed_bw_main                     []
% 7.40/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.40/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.40/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.40/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.40/1.52  
% 7.40/1.52  ------ Combination Options
% 7.40/1.52  
% 7.40/1.52  --comb_res_mult                         3
% 7.40/1.52  --comb_sup_mult                         2
% 7.40/1.52  --comb_inst_mult                        10
% 7.40/1.52  
% 7.40/1.52  ------ Debug Options
% 7.40/1.52  
% 7.40/1.52  --dbg_backtrace                         false
% 7.40/1.52  --dbg_dump_prop_clauses                 false
% 7.40/1.52  --dbg_dump_prop_clauses_file            -
% 7.40/1.52  --dbg_out_stat                          false
% 7.40/1.52  ------ Parsing...
% 7.40/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.40/1.52  
% 7.40/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 7.40/1.52  
% 7.40/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.40/1.52  
% 7.40/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.40/1.52  ------ Proving...
% 7.40/1.52  ------ Problem Properties 
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  clauses                                 38
% 7.40/1.52  conjectures                             8
% 7.40/1.52  EPR                                     8
% 7.40/1.52  Horn                                    36
% 7.40/1.52  unary                                   3
% 7.40/1.52  binary                                  16
% 7.40/1.52  lits                                    98
% 7.40/1.52  lits eq                                 13
% 7.40/1.52  fd_pure                                 0
% 7.40/1.52  fd_pseudo                               0
% 7.40/1.52  fd_cond                                 0
% 7.40/1.52  fd_pseudo_cond                          1
% 7.40/1.52  AC symbols                              0
% 7.40/1.52  
% 7.40/1.52  ------ Schedule dynamic 5 is on 
% 7.40/1.52  
% 7.40/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  ------ 
% 7.40/1.52  Current options:
% 7.40/1.52  ------ 
% 7.40/1.52  
% 7.40/1.52  ------ Input Options
% 7.40/1.52  
% 7.40/1.52  --out_options                           all
% 7.40/1.52  --tptp_safe_out                         true
% 7.40/1.52  --problem_path                          ""
% 7.40/1.52  --include_path                          ""
% 7.40/1.52  --clausifier                            res/vclausify_rel
% 7.40/1.52  --clausifier_options                    --mode clausify
% 7.40/1.52  --stdin                                 false
% 7.40/1.52  --stats_out                             all
% 7.40/1.52  
% 7.40/1.52  ------ General Options
% 7.40/1.52  
% 7.40/1.52  --fof                                   false
% 7.40/1.52  --time_out_real                         305.
% 7.40/1.52  --time_out_virtual                      -1.
% 7.40/1.52  --symbol_type_check                     false
% 7.40/1.52  --clausify_out                          false
% 7.40/1.52  --sig_cnt_out                           false
% 7.40/1.52  --trig_cnt_out                          false
% 7.40/1.52  --trig_cnt_out_tolerance                1.
% 7.40/1.52  --trig_cnt_out_sk_spl                   false
% 7.40/1.52  --abstr_cl_out                          false
% 7.40/1.52  
% 7.40/1.52  ------ Global Options
% 7.40/1.52  
% 7.40/1.52  --schedule                              default
% 7.40/1.52  --add_important_lit                     false
% 7.40/1.52  --prop_solver_per_cl                    1000
% 7.40/1.52  --min_unsat_core                        false
% 7.40/1.52  --soft_assumptions                      false
% 7.40/1.52  --soft_lemma_size                       3
% 7.40/1.52  --prop_impl_unit_size                   0
% 7.40/1.52  --prop_impl_unit                        []
% 7.40/1.52  --share_sel_clauses                     true
% 7.40/1.52  --reset_solvers                         false
% 7.40/1.52  --bc_imp_inh                            [conj_cone]
% 7.40/1.52  --conj_cone_tolerance                   3.
% 7.40/1.52  --extra_neg_conj                        none
% 7.40/1.52  --large_theory_mode                     true
% 7.40/1.52  --prolific_symb_bound                   200
% 7.40/1.52  --lt_threshold                          2000
% 7.40/1.52  --clause_weak_htbl                      true
% 7.40/1.52  --gc_record_bc_elim                     false
% 7.40/1.52  
% 7.40/1.52  ------ Preprocessing Options
% 7.40/1.52  
% 7.40/1.52  --preprocessing_flag                    true
% 7.40/1.52  --time_out_prep_mult                    0.1
% 7.40/1.52  --splitting_mode                        input
% 7.40/1.52  --splitting_grd                         true
% 7.40/1.52  --splitting_cvd                         false
% 7.40/1.52  --splitting_cvd_svl                     false
% 7.40/1.52  --splitting_nvd                         32
% 7.40/1.52  --sub_typing                            true
% 7.40/1.52  --prep_gs_sim                           true
% 7.40/1.52  --prep_unflatten                        true
% 7.40/1.52  --prep_res_sim                          true
% 7.40/1.52  --prep_upred                            true
% 7.40/1.52  --prep_sem_filter                       exhaustive
% 7.40/1.52  --prep_sem_filter_out                   false
% 7.40/1.52  --pred_elim                             true
% 7.40/1.52  --res_sim_input                         true
% 7.40/1.52  --eq_ax_congr_red                       true
% 7.40/1.52  --pure_diseq_elim                       true
% 7.40/1.52  --brand_transform                       false
% 7.40/1.52  --non_eq_to_eq                          false
% 7.40/1.52  --prep_def_merge                        true
% 7.40/1.52  --prep_def_merge_prop_impl              false
% 7.40/1.52  --prep_def_merge_mbd                    true
% 7.40/1.52  --prep_def_merge_tr_red                 false
% 7.40/1.52  --prep_def_merge_tr_cl                  false
% 7.40/1.52  --smt_preprocessing                     true
% 7.40/1.52  --smt_ac_axioms                         fast
% 7.40/1.52  --preprocessed_out                      false
% 7.40/1.52  --preprocessed_stats                    false
% 7.40/1.52  
% 7.40/1.52  ------ Abstraction refinement Options
% 7.40/1.52  
% 7.40/1.52  --abstr_ref                             []
% 7.40/1.52  --abstr_ref_prep                        false
% 7.40/1.52  --abstr_ref_until_sat                   false
% 7.40/1.52  --abstr_ref_sig_restrict                funpre
% 7.40/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.40/1.52  --abstr_ref_under                       []
% 7.40/1.52  
% 7.40/1.52  ------ SAT Options
% 7.40/1.52  
% 7.40/1.52  --sat_mode                              false
% 7.40/1.52  --sat_fm_restart_options                ""
% 7.40/1.52  --sat_gr_def                            false
% 7.40/1.52  --sat_epr_types                         true
% 7.40/1.52  --sat_non_cyclic_types                  false
% 7.40/1.52  --sat_finite_models                     false
% 7.40/1.52  --sat_fm_lemmas                         false
% 7.40/1.52  --sat_fm_prep                           false
% 7.40/1.52  --sat_fm_uc_incr                        true
% 7.40/1.52  --sat_out_model                         small
% 7.40/1.52  --sat_out_clauses                       false
% 7.40/1.52  
% 7.40/1.52  ------ QBF Options
% 7.40/1.52  
% 7.40/1.52  --qbf_mode                              false
% 7.40/1.52  --qbf_elim_univ                         false
% 7.40/1.52  --qbf_dom_inst                          none
% 7.40/1.52  --qbf_dom_pre_inst                      false
% 7.40/1.52  --qbf_sk_in                             false
% 7.40/1.52  --qbf_pred_elim                         true
% 7.40/1.52  --qbf_split                             512
% 7.40/1.52  
% 7.40/1.52  ------ BMC1 Options
% 7.40/1.52  
% 7.40/1.52  --bmc1_incremental                      false
% 7.40/1.52  --bmc1_axioms                           reachable_all
% 7.40/1.52  --bmc1_min_bound                        0
% 7.40/1.52  --bmc1_max_bound                        -1
% 7.40/1.52  --bmc1_max_bound_default                -1
% 7.40/1.52  --bmc1_symbol_reachability              true
% 7.40/1.52  --bmc1_property_lemmas                  false
% 7.40/1.52  --bmc1_k_induction                      false
% 7.40/1.52  --bmc1_non_equiv_states                 false
% 7.40/1.52  --bmc1_deadlock                         false
% 7.40/1.52  --bmc1_ucm                              false
% 7.40/1.52  --bmc1_add_unsat_core                   none
% 7.40/1.52  --bmc1_unsat_core_children              false
% 7.40/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.40/1.52  --bmc1_out_stat                         full
% 7.40/1.52  --bmc1_ground_init                      false
% 7.40/1.52  --bmc1_pre_inst_next_state              false
% 7.40/1.52  --bmc1_pre_inst_state                   false
% 7.40/1.52  --bmc1_pre_inst_reach_state             false
% 7.40/1.52  --bmc1_out_unsat_core                   false
% 7.40/1.52  --bmc1_aig_witness_out                  false
% 7.40/1.52  --bmc1_verbose                          false
% 7.40/1.52  --bmc1_dump_clauses_tptp                false
% 7.40/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.40/1.52  --bmc1_dump_file                        -
% 7.40/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.40/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.40/1.52  --bmc1_ucm_extend_mode                  1
% 7.40/1.52  --bmc1_ucm_init_mode                    2
% 7.40/1.52  --bmc1_ucm_cone_mode                    none
% 7.40/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.40/1.52  --bmc1_ucm_relax_model                  4
% 7.40/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.40/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.40/1.52  --bmc1_ucm_layered_model                none
% 7.40/1.52  --bmc1_ucm_max_lemma_size               10
% 7.40/1.52  
% 7.40/1.52  ------ AIG Options
% 7.40/1.52  
% 7.40/1.52  --aig_mode                              false
% 7.40/1.52  
% 7.40/1.52  ------ Instantiation Options
% 7.40/1.52  
% 7.40/1.52  --instantiation_flag                    true
% 7.40/1.52  --inst_sos_flag                         false
% 7.40/1.52  --inst_sos_phase                        true
% 7.40/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.40/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.40/1.52  --inst_lit_sel_side                     none
% 7.40/1.52  --inst_solver_per_active                1400
% 7.40/1.52  --inst_solver_calls_frac                1.
% 7.40/1.52  --inst_passive_queue_type               priority_queues
% 7.40/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.40/1.52  --inst_passive_queues_freq              [25;2]
% 7.40/1.52  --inst_dismatching                      true
% 7.40/1.52  --inst_eager_unprocessed_to_passive     true
% 7.40/1.52  --inst_prop_sim_given                   true
% 7.40/1.52  --inst_prop_sim_new                     false
% 7.40/1.52  --inst_subs_new                         false
% 7.40/1.52  --inst_eq_res_simp                      false
% 7.40/1.52  --inst_subs_given                       false
% 7.40/1.52  --inst_orphan_elimination               true
% 7.40/1.52  --inst_learning_loop_flag               true
% 7.40/1.52  --inst_learning_start                   3000
% 7.40/1.52  --inst_learning_factor                  2
% 7.40/1.52  --inst_start_prop_sim_after_learn       3
% 7.40/1.52  --inst_sel_renew                        solver
% 7.40/1.52  --inst_lit_activity_flag                true
% 7.40/1.52  --inst_restr_to_given                   false
% 7.40/1.52  --inst_activity_threshold               500
% 7.40/1.52  --inst_out_proof                        true
% 7.40/1.52  
% 7.40/1.52  ------ Resolution Options
% 7.40/1.52  
% 7.40/1.52  --resolution_flag                       false
% 7.40/1.52  --res_lit_sel                           adaptive
% 7.40/1.52  --res_lit_sel_side                      none
% 7.40/1.52  --res_ordering                          kbo
% 7.40/1.52  --res_to_prop_solver                    active
% 7.40/1.52  --res_prop_simpl_new                    false
% 7.40/1.52  --res_prop_simpl_given                  true
% 7.40/1.52  --res_passive_queue_type                priority_queues
% 7.40/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.40/1.52  --res_passive_queues_freq               [15;5]
% 7.40/1.52  --res_forward_subs                      full
% 7.40/1.52  --res_backward_subs                     full
% 7.40/1.52  --res_forward_subs_resolution           true
% 7.40/1.52  --res_backward_subs_resolution          true
% 7.40/1.52  --res_orphan_elimination                true
% 7.40/1.52  --res_time_limit                        2.
% 7.40/1.52  --res_out_proof                         true
% 7.40/1.52  
% 7.40/1.52  ------ Superposition Options
% 7.40/1.52  
% 7.40/1.52  --superposition_flag                    true
% 7.40/1.52  --sup_passive_queue_type                priority_queues
% 7.40/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.40/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.40/1.52  --demod_completeness_check              fast
% 7.40/1.52  --demod_use_ground                      true
% 7.40/1.52  --sup_to_prop_solver                    passive
% 7.40/1.52  --sup_prop_simpl_new                    true
% 7.40/1.52  --sup_prop_simpl_given                  true
% 7.40/1.52  --sup_fun_splitting                     false
% 7.40/1.52  --sup_smt_interval                      50000
% 7.40/1.52  
% 7.40/1.52  ------ Superposition Simplification Setup
% 7.40/1.52  
% 7.40/1.52  --sup_indices_passive                   []
% 7.40/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.40/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.40/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.40/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.40/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.40/1.52  --sup_full_bw                           [BwDemod]
% 7.40/1.52  --sup_immed_triv                        [TrivRules]
% 7.40/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.40/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.40/1.52  --sup_immed_bw_main                     []
% 7.40/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.40/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.40/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.40/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.40/1.52  
% 7.40/1.52  ------ Combination Options
% 7.40/1.52  
% 7.40/1.52  --comb_res_mult                         3
% 7.40/1.52  --comb_sup_mult                         2
% 7.40/1.52  --comb_inst_mult                        10
% 7.40/1.52  
% 7.40/1.52  ------ Debug Options
% 7.40/1.52  
% 7.40/1.52  --dbg_backtrace                         false
% 7.40/1.52  --dbg_dump_prop_clauses                 false
% 7.40/1.52  --dbg_dump_prop_clauses_file            -
% 7.40/1.52  --dbg_out_stat                          false
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  ------ Proving...
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  % SZS status Theorem for theBenchmark.p
% 7.40/1.52  
% 7.40/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.40/1.52  
% 7.40/1.52  fof(f15,conjecture,(
% 7.40/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f16,negated_conjecture,(
% 7.40/1.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 7.40/1.52    inference(negated_conjecture,[],[f15])).
% 7.40/1.52  
% 7.40/1.52  fof(f35,plain,(
% 7.40/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.40/1.52    inference(ennf_transformation,[],[f16])).
% 7.40/1.52  
% 7.40/1.52  fof(f36,plain,(
% 7.40/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.40/1.52    inference(flattening,[],[f35])).
% 7.40/1.52  
% 7.40/1.52  fof(f46,plain,(
% 7.40/1.52    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.40/1.52    introduced(choice_axiom,[])).
% 7.40/1.52  
% 7.40/1.52  fof(f45,plain,(
% 7.40/1.52    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.40/1.52    introduced(choice_axiom,[])).
% 7.40/1.52  
% 7.40/1.52  fof(f44,plain,(
% 7.40/1.52    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 7.40/1.52    introduced(choice_axiom,[])).
% 7.40/1.52  
% 7.40/1.52  fof(f43,plain,(
% 7.40/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.40/1.52    introduced(choice_axiom,[])).
% 7.40/1.52  
% 7.40/1.52  fof(f47,plain,(
% 7.40/1.52    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.40/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f46,f45,f44,f43])).
% 7.40/1.52  
% 7.40/1.52  fof(f72,plain,(
% 7.40/1.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f2,axiom,(
% 7.40/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f17,plain,(
% 7.40/1.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.40/1.52    inference(ennf_transformation,[],[f2])).
% 7.40/1.52  
% 7.40/1.52  fof(f51,plain,(
% 7.40/1.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.40/1.52    inference(cnf_transformation,[],[f17])).
% 7.40/1.52  
% 7.40/1.52  fof(f7,axiom,(
% 7.40/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f24,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(ennf_transformation,[],[f7])).
% 7.40/1.52  
% 7.40/1.52  fof(f57,plain,(
% 7.40/1.52    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f24])).
% 7.40/1.52  
% 7.40/1.52  fof(f70,plain,(
% 7.40/1.52    l1_pre_topc(sK0)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f3,axiom,(
% 7.40/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f18,plain,(
% 7.40/1.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.40/1.52    inference(ennf_transformation,[],[f3])).
% 7.40/1.52  
% 7.40/1.52  fof(f52,plain,(
% 7.40/1.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.40/1.52    inference(cnf_transformation,[],[f18])).
% 7.40/1.52  
% 7.40/1.52  fof(f12,axiom,(
% 7.40/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f31,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(ennf_transformation,[],[f12])).
% 7.40/1.52  
% 7.40/1.52  fof(f42,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(nnf_transformation,[],[f31])).
% 7.40/1.52  
% 7.40/1.52  fof(f66,plain,(
% 7.40/1.52    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f42])).
% 7.40/1.52  
% 7.40/1.52  fof(f6,axiom,(
% 7.40/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f22,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(ennf_transformation,[],[f6])).
% 7.40/1.52  
% 7.40/1.52  fof(f23,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(flattening,[],[f22])).
% 7.40/1.52  
% 7.40/1.52  fof(f55,plain,(
% 7.40/1.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f23])).
% 7.40/1.52  
% 7.40/1.52  fof(f4,axiom,(
% 7.40/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f19,plain,(
% 7.40/1.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.40/1.52    inference(ennf_transformation,[],[f4])).
% 7.40/1.52  
% 7.40/1.52  fof(f20,plain,(
% 7.40/1.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(flattening,[],[f19])).
% 7.40/1.52  
% 7.40/1.52  fof(f53,plain,(
% 7.40/1.52    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f20])).
% 7.40/1.52  
% 7.40/1.52  fof(f11,axiom,(
% 7.40/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f29,plain,(
% 7.40/1.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.40/1.52    inference(ennf_transformation,[],[f11])).
% 7.40/1.52  
% 7.40/1.52  fof(f30,plain,(
% 7.40/1.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.40/1.52    inference(flattening,[],[f29])).
% 7.40/1.52  
% 7.40/1.52  fof(f64,plain,(
% 7.40/1.52    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f30])).
% 7.40/1.52  
% 7.40/1.52  fof(f69,plain,(
% 7.40/1.52    v2_pre_topc(sK0)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f9,axiom,(
% 7.40/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f26,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(ennf_transformation,[],[f9])).
% 7.40/1.52  
% 7.40/1.52  fof(f41,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(nnf_transformation,[],[f26])).
% 7.40/1.52  
% 7.40/1.52  fof(f61,plain,(
% 7.40/1.52    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f41])).
% 7.40/1.52  
% 7.40/1.52  fof(f73,plain,(
% 7.40/1.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f74,plain,(
% 7.40/1.52    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f75,plain,(
% 7.40/1.52    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f76,plain,(
% 7.40/1.52    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f71,plain,(
% 7.40/1.52    l1_pre_topc(sK1)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f5,axiom,(
% 7.40/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f21,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(ennf_transformation,[],[f5])).
% 7.40/1.52  
% 7.40/1.52  fof(f54,plain,(
% 7.40/1.52    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f21])).
% 7.40/1.52  
% 7.40/1.52  fof(f62,plain,(
% 7.40/1.52    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f41])).
% 7.40/1.52  
% 7.40/1.52  fof(f1,axiom,(
% 7.40/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f37,plain,(
% 7.40/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.40/1.52    inference(nnf_transformation,[],[f1])).
% 7.40/1.52  
% 7.40/1.52  fof(f38,plain,(
% 7.40/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.40/1.52    inference(flattening,[],[f37])).
% 7.40/1.52  
% 7.40/1.52  fof(f50,plain,(
% 7.40/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f38])).
% 7.40/1.52  
% 7.40/1.52  fof(f8,axiom,(
% 7.40/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f25,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(ennf_transformation,[],[f8])).
% 7.40/1.52  
% 7.40/1.52  fof(f39,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(nnf_transformation,[],[f25])).
% 7.40/1.52  
% 7.40/1.52  fof(f40,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(flattening,[],[f39])).
% 7.40/1.52  
% 7.40/1.52  fof(f58,plain,(
% 7.40/1.52    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f40])).
% 7.40/1.52  
% 7.40/1.52  fof(f13,axiom,(
% 7.40/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 7.40/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.40/1.52  
% 7.40/1.52  fof(f32,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(ennf_transformation,[],[f13])).
% 7.40/1.52  
% 7.40/1.52  fof(f33,plain,(
% 7.40/1.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.40/1.52    inference(flattening,[],[f32])).
% 7.40/1.52  
% 7.40/1.52  fof(f67,plain,(
% 7.40/1.52    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f33])).
% 7.40/1.52  
% 7.40/1.52  fof(f60,plain,(
% 7.40/1.52    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.40/1.52    inference(cnf_transformation,[],[f40])).
% 7.40/1.52  
% 7.40/1.52  fof(f78,plain,(
% 7.40/1.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f79,plain,(
% 7.40/1.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f77,plain,(
% 7.40/1.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 7.40/1.52    inference(cnf_transformation,[],[f47])).
% 7.40/1.52  
% 7.40/1.52  fof(f48,plain,(
% 7.40/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.40/1.52    inference(cnf_transformation,[],[f38])).
% 7.40/1.52  
% 7.40/1.52  fof(f81,plain,(
% 7.40/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.40/1.52    inference(equality_resolution,[],[f48])).
% 7.40/1.52  
% 7.40/1.52  cnf(c_28,negated_conjecture,
% 7.40/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.40/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1561,plain,
% 7.40/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_3,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.40/1.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.40/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1570,plain,
% 7.40/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.40/1.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_9,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ l1_pre_topc(X1)
% 7.40/1.52      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_30,negated_conjecture,
% 7.40/1.52      ( l1_pre_topc(sK0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_753,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 7.40/1.52      | sK0 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_754,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_753]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1537,plain,
% 7.40/1.52      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2800,plain,
% 7.40/1.52      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1570,c_1537]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_9004,plain,
% 7.40/1.52      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0))))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)))
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1570,c_2800]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_24657,plain,
% 7.40/1.52      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1561,c_9004]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_4,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.40/1.52      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.40/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1569,plain,
% 7.40/1.52      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.40/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2243,plain,
% 7.40/1.52      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1561,c_1569]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_17,plain,
% 7.40/1.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.40/1.52      | v4_pre_topc(X1,X0)
% 7.40/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.40/1.52      | ~ l1_pre_topc(X0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_8,plain,
% 7.40/1.52      ( ~ v4_pre_topc(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ l1_pre_topc(X1)
% 7.40/1.52      | k2_pre_topc(X1,X0) = X0 ),
% 7.40/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_391,plain,
% 7.40/1.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.40/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.40/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.40/1.52      | ~ l1_pre_topc(X0)
% 7.40/1.52      | ~ l1_pre_topc(X3)
% 7.40/1.52      | X2 != X1
% 7.40/1.52      | X3 != X0
% 7.40/1.52      | k2_pre_topc(X3,X2) = X2 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_17,c_8]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_392,plain,
% 7.40/1.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.40/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.40/1.52      | ~ l1_pre_topc(X0)
% 7.40/1.52      | k2_pre_topc(X0,X1) = X1 ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_391]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_456,plain,
% 7.40/1.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.40/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.40/1.52      | k2_pre_topc(X0,X1) = X1
% 7.40/1.52      | sK0 != X0 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_392,c_30]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_457,plain,
% 7.40/1.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | k2_pre_topc(sK0,X0) = X0 ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_456]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1557,plain,
% 7.40/1.52      ( k2_pre_topc(sK0,X0) = X0
% 7.40/1.52      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_4691,plain,
% 7.40/1.52      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2)
% 7.40/1.52      | v3_pre_topc(sK2,sK0) != iProver_top
% 7.40/1.52      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_2243,c_1557]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_35,plain,
% 7.40/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_5,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ l1_pre_topc(X1) ),
% 7.40/1.52      inference(cnf_transformation,[],[f53]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_777,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | sK0 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_5,c_30]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_778,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_777]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1866,plain,
% 7.40/1.52      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_778]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1867,plain,
% 7.40/1.52      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.40/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_1866]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1929,plain,
% 7.40/1.52      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1930,plain,
% 7.40/1.52      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.40/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2199,plain,
% 7.40/1.52      ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2200,plain,
% 7.40/1.52      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.40/1.52      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_2199]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1535,plain,
% 7.40/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.40/1.52      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2244,plain,
% 7.40/1.52      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1535,c_1569]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_4099,plain,
% 7.40/1.52      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,sK2) ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1561,c_2244]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_16,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.40/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.40/1.52      | ~ v2_pre_topc(X0)
% 7.40/1.52      | ~ l1_pre_topc(X0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_31,negated_conjecture,
% 7.40/1.52      ( v2_pre_topc(sK0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_344,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.40/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.40/1.52      | ~ l1_pre_topc(X0)
% 7.40/1.52      | sK0 != X0 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_345,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | ~ l1_pre_topc(sK0) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_344]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_349,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 7.40/1.52      inference(global_propositional_subsumption,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_345,c_30]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_350,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.40/1.52      inference(renaming,[status(thm)],[c_349]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1560,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2747,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1570,c_1560]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_4127,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_4099,c_2747]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_14,plain,
% 7.40/1.52      ( ~ v6_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ l1_pre_topc(X1)
% 7.40/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 7.40/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_675,plain,
% 7.40/1.52      ( ~ v6_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
% 7.40/1.52      | sK0 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_676,plain,
% 7.40/1.52      ( ~ v6_tops_1(X0,sK0)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_675]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1542,plain,
% 7.40/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
% 7.40/1.52      | v6_tops_1(X0,sK0) != iProver_top
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_3545,plain,
% 7.40/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 7.40/1.52      | v6_tops_1(sK2,sK0) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1561,c_1542]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_27,negated_conjecture,
% 7.40/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.40/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_36,plain,
% 7.40/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_26,negated_conjecture,
% 7.40/1.52      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_37,plain,
% 7.40/1.52      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.40/1.52      | v6_tops_1(sK2,sK0) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_25,negated_conjecture,
% 7.40/1.52      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 7.40/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_38,plain,
% 7.40/1.52      ( v6_tops_1(sK2,sK0) = iProver_top
% 7.40/1.52      | v4_tops_1(sK3,sK1) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_24,negated_conjecture,
% 7.40/1.52      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_39,plain,
% 7.40/1.52      ( v6_tops_1(sK3,sK1) != iProver_top
% 7.40/1.52      | v6_tops_1(sK2,sK0) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_29,negated_conjecture,
% 7.40/1.52      ( l1_pre_topc(sK1) ),
% 7.40/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_618,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | sK1 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_5,c_29]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_619,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_618]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1860,plain,
% 7.40/1.52      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_619]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1861,plain,
% 7.40/1.52      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.40/1.52      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_6,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.40/1.52      | ~ l1_pre_topc(X1) ),
% 7.40/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_606,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.40/1.52      | sK1 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_607,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_606]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1875,plain,
% 7.40/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_607]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1876,plain,
% 7.40/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.40/1.52      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_1875]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_13,plain,
% 7.40/1.52      ( v6_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ l1_pre_topc(X1)
% 7.40/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 7.40/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_531,plain,
% 7.40/1.52      ( v6_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 7.40/1.52      | sK1 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_532,plain,
% 7.40/1.52      ( v6_tops_1(X0,sK1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_531]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1900,plain,
% 7.40/1.52      ( v6_tops_1(sK3,sK1)
% 7.40/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_532]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1901,plain,
% 7.40/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
% 7.40/1.52      | v6_tops_1(sK3,sK1) = iProver_top
% 7.40/1.52      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_1900]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1903,plain,
% 7.40/1.52      ( ~ v6_tops_1(sK2,sK0)
% 7.40/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_676]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1904,plain,
% 7.40/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 7.40/1.52      | v6_tops_1(sK2,sK0) != iProver_top
% 7.40/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_0,plain,
% 7.40/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.40/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2263,plain,
% 7.40/1.52      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
% 7.40/1.52      | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.40/1.52      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2264,plain,
% 7.40/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 7.40/1.52      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
% 7.40/1.52      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_2263]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_12,plain,
% 7.40/1.52      ( ~ v4_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.40/1.52      | ~ l1_pre_topc(X1) ),
% 7.40/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_546,plain,
% 7.40/1.52      ( ~ v4_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.40/1.52      | sK1 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_547,plain,
% 7.40/1.52      ( ~ v4_tops_1(X0,sK1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_546]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2274,plain,
% 7.40/1.52      ( ~ v4_tops_1(sK3,sK1)
% 7.40/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_547]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2275,plain,
% 7.40/1.52      ( v4_tops_1(sK3,sK1) != iProver_top
% 7.40/1.52      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.40/1.52      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_2274]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_19,plain,
% 7.40/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ r1_tarski(X0,X2)
% 7.40/1.52      | r1_tarski(X0,k1_tops_1(X1,X2))
% 7.40/1.52      | ~ l1_pre_topc(X1) ),
% 7.40/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_483,plain,
% 7.40/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ r1_tarski(X0,X2)
% 7.40/1.52      | r1_tarski(X0,k1_tops_1(X1,X2))
% 7.40/1.52      | sK1 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_484,plain,
% 7.40/1.52      ( ~ v3_pre_topc(X0,sK1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | ~ r1_tarski(X0,X1)
% 7.40/1.52      | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_483]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2292,plain,
% 7.40/1.52      ( ~ v3_pre_topc(sK3,sK1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | ~ r1_tarski(sK3,X0)
% 7.40/1.52      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_484]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2723,plain,
% 7.40/1.52      ( ~ v3_pre_topc(sK3,sK1)
% 7.40/1.52      | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.40/1.52      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.40/1.52      | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_2292]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2724,plain,
% 7.40/1.52      ( v3_pre_topc(sK3,sK1) != iProver_top
% 7.40/1.52      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.40/1.52      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.40/1.52      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
% 7.40/1.52      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_2723]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_3611,plain,
% 7.40/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 7.40/1.52      inference(global_propositional_subsumption,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_3545,c_35,c_36,c_37,c_38,c_39,c_1861,c_1876,c_1901,
% 7.40/1.52                 c_1904,c_2264,c_2275,c_2724]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_4130,plain,
% 7.40/1.52      ( v3_pre_topc(sK2,sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(light_normalisation,[status(thm)],[c_4127,c_3611]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_23742,plain,
% 7.40/1.52      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),sK2) ),
% 7.40/1.52      inference(global_propositional_subsumption,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_4691,c_35,c_1867,c_1930,c_2200,c_4130]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_24693,plain,
% 7.40/1.52      ( k1_tops_1(sK0,sK2) = sK2 ),
% 7.40/1.52      inference(light_normalisation,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_24657,c_2243,c_23742]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_10,plain,
% 7.40/1.52      ( v4_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.40/1.52      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.40/1.52      | ~ l1_pre_topc(X1) ),
% 7.40/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_735,plain,
% 7.40/1.52      ( v4_tops_1(X0,X1)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.40/1.52      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.40/1.52      | sK0 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_736,plain,
% 7.40/1.52      ( v4_tops_1(X0,sK0)
% 7.40/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 7.40/1.52      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_735]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1538,plain,
% 7.40/1.52      ( v4_tops_1(X0,sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.40/1.52      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 7.40/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_3626,plain,
% 7.40/1.52      ( v4_tops_1(sK2,sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.40/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 7.40/1.52      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_3611,c_1538]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2749,plain,
% 7.40/1.52      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_1535,c_1560]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_7045,plain,
% 7.40/1.52      ( v3_pre_topc(sK2,sK0) = iProver_top
% 7.40/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_3611,c_2749]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_7058,plain,
% 7.40/1.52      ( v3_pre_topc(sK2,sK0) = iProver_top ),
% 7.40/1.52      inference(global_propositional_subsumption,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_7045,c_35,c_1867,c_2200,c_4130]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_22,negated_conjecture,
% 7.40/1.52      ( ~ v3_pre_topc(sK2,sK0)
% 7.40/1.52      | v4_tops_1(sK3,sK1)
% 7.40/1.52      | ~ v4_tops_1(sK2,sK0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1567,plain,
% 7.40/1.52      ( v3_pre_topc(sK2,sK0) != iProver_top
% 7.40/1.52      | v4_tops_1(sK3,sK1) = iProver_top
% 7.40/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_7063,plain,
% 7.40/1.52      ( v4_tops_1(sK3,sK1) = iProver_top
% 7.40/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_7058,c_1567]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_21,negated_conjecture,
% 7.40/1.52      ( ~ v3_pre_topc(sK2,sK0)
% 7.40/1.52      | ~ v6_tops_1(sK3,sK1)
% 7.40/1.52      | ~ v4_tops_1(sK2,sK0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_42,plain,
% 7.40/1.52      ( v3_pre_topc(sK2,sK0) != iProver_top
% 7.40/1.52      | v6_tops_1(sK3,sK1) != iProver_top
% 7.40/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_23,negated_conjecture,
% 7.40/1.52      ( v3_pre_topc(sK3,sK1)
% 7.40/1.52      | ~ v3_pre_topc(sK2,sK0)
% 7.40/1.52      | ~ v4_tops_1(sK2,sK0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1566,plain,
% 7.40/1.52      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.40/1.52      | v3_pre_topc(sK2,sK0) != iProver_top
% 7.40/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_7064,plain,
% 7.40/1.52      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.40/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.40/1.52      inference(superposition,[status(thm)],[c_7058,c_1566]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_7176,plain,
% 7.40/1.52      ( v4_tops_1(sK2,sK0) != iProver_top ),
% 7.40/1.52      inference(global_propositional_subsumption,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_7063,c_35,c_36,c_42,c_1861,c_1867,c_1876,c_1901,
% 7.40/1.52                 c_2200,c_2264,c_2275,c_2724,c_4130,c_7064]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_16365,plain,
% 7.40/1.52      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 7.40/1.52      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.40/1.52      inference(global_propositional_subsumption,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_3626,c_35,c_36,c_42,c_1861,c_1867,c_1876,c_1901,
% 7.40/1.52                 c_2200,c_2264,c_2275,c_2724,c_4130,c_7063,c_7064]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_2,plain,
% 7.40/1.52      ( r1_tarski(X0,X0) ),
% 7.40/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1571,plain,
% 7.40/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_16371,plain,
% 7.40/1.52      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 7.40/1.52      inference(forward_subsumption_resolution,
% 7.40/1.52                [status(thm)],
% 7.40/1.52                [c_16365,c_1571]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_26833,plain,
% 7.40/1.52      ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 7.40/1.52      inference(demodulation,[status(thm)],[c_24693,c_16371]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_765,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.40/1.52      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.40/1.52      | sK0 != X1 ),
% 7.40/1.52      inference(resolution_lifted,[status(thm)],[c_6,c_30]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_766,plain,
% 7.40/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 7.40/1.52      inference(unflattening,[status(thm)],[c_765]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1884,plain,
% 7.40/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.40/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
% 7.40/1.52      inference(instantiation,[status(thm)],[c_766]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(c_1885,plain,
% 7.40/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.40/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 7.40/1.52      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 7.40/1.52  
% 7.40/1.52  cnf(contradiction,plain,
% 7.40/1.52      ( $false ),
% 7.40/1.52      inference(minisat,[status(thm)],[c_26833,c_1885,c_35]) ).
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.40/1.52  
% 7.40/1.52  ------                               Statistics
% 7.40/1.52  
% 7.40/1.52  ------ General
% 7.40/1.52  
% 7.40/1.52  abstr_ref_over_cycles:                  0
% 7.40/1.52  abstr_ref_under_cycles:                 0
% 7.40/1.52  gc_basic_clause_elim:                   0
% 7.40/1.52  forced_gc_time:                         0
% 7.40/1.52  parsing_time:                           0.009
% 7.40/1.52  unif_index_cands_time:                  0.
% 7.40/1.52  unif_index_add_time:                    0.
% 7.40/1.52  orderings_time:                         0.
% 7.40/1.52  out_proof_time:                         0.017
% 7.40/1.52  total_time:                             0.893
% 7.40/1.52  num_of_symbols:                         48
% 7.40/1.52  num_of_terms:                           28063
% 7.40/1.52  
% 7.40/1.52  ------ Preprocessing
% 7.40/1.52  
% 7.40/1.52  num_of_splits:                          0
% 7.40/1.52  num_of_split_atoms:                     0
% 7.40/1.52  num_of_reused_defs:                     0
% 7.40/1.52  num_eq_ax_congr_red:                    4
% 7.40/1.52  num_of_sem_filtered_clauses:            1
% 7.40/1.52  num_of_subtypes:                        0
% 7.40/1.52  monotx_restored_types:                  0
% 7.40/1.52  sat_num_of_epr_types:                   0
% 7.40/1.52  sat_num_of_non_cyclic_types:            0
% 7.40/1.52  sat_guarded_non_collapsed_types:        0
% 7.40/1.52  num_pure_diseq_elim:                    0
% 7.40/1.52  simp_replaced_by:                       0
% 7.40/1.52  res_preprocessed:                       132
% 7.40/1.52  prep_upred:                             0
% 7.40/1.52  prep_unflattend:                        32
% 7.40/1.52  smt_new_axioms:                         0
% 7.40/1.52  pred_elim_cands:                        8
% 7.40/1.52  pred_elim:                              3
% 7.40/1.52  pred_elim_cl:                           -7
% 7.40/1.52  pred_elim_cycles:                       4
% 7.40/1.52  merged_defs:                            0
% 7.40/1.52  merged_defs_ncl:                        0
% 7.40/1.52  bin_hyper_res:                          0
% 7.40/1.52  prep_cycles:                            3
% 7.40/1.52  pred_elim_time:                         0.011
% 7.40/1.52  splitting_time:                         0.
% 7.40/1.52  sem_filter_time:                        0.
% 7.40/1.52  monotx_time:                            0.001
% 7.40/1.52  subtype_inf_time:                       0.
% 7.40/1.52  
% 7.40/1.52  ------ Problem properties
% 7.40/1.52  
% 7.40/1.52  clauses:                                38
% 7.40/1.52  conjectures:                            8
% 7.40/1.52  epr:                                    8
% 7.40/1.52  horn:                                   36
% 7.40/1.52  ground:                                 8
% 7.40/1.52  unary:                                  3
% 7.40/1.52  binary:                                 16
% 7.40/1.52  lits:                                   98
% 7.40/1.52  lits_eq:                                13
% 7.40/1.52  fd_pure:                                0
% 7.40/1.52  fd_pseudo:                              0
% 7.40/1.52  fd_cond:                                0
% 7.40/1.52  fd_pseudo_cond:                         1
% 7.40/1.52  ac_symbols:                             0
% 7.40/1.52  
% 7.40/1.52  ------ Propositional Solver
% 7.40/1.52  
% 7.40/1.52  prop_solver_calls:                      27
% 7.40/1.52  prop_fast_solver_calls:                 1449
% 7.40/1.52  smt_solver_calls:                       0
% 7.40/1.52  smt_fast_solver_calls:                  0
% 7.40/1.52  prop_num_of_clauses:                    10854
% 7.40/1.52  prop_preprocess_simplified:             21769
% 7.40/1.52  prop_fo_subsumed:                       65
% 7.40/1.52  prop_solver_time:                       0.
% 7.40/1.52  smt_solver_time:                        0.
% 7.40/1.52  smt_fast_solver_time:                   0.
% 7.40/1.52  prop_fast_solver_time:                  0.
% 7.40/1.52  prop_unsat_core_time:                   0.001
% 7.40/1.52  
% 7.40/1.52  ------ QBF
% 7.40/1.52  
% 7.40/1.52  qbf_q_res:                              0
% 7.40/1.52  qbf_num_tautologies:                    0
% 7.40/1.52  qbf_prep_cycles:                        0
% 7.40/1.52  
% 7.40/1.52  ------ BMC1
% 7.40/1.52  
% 7.40/1.52  bmc1_current_bound:                     -1
% 7.40/1.52  bmc1_last_solved_bound:                 -1
% 7.40/1.52  bmc1_unsat_core_size:                   -1
% 7.40/1.52  bmc1_unsat_core_parents_size:           -1
% 7.40/1.52  bmc1_merge_next_fun:                    0
% 7.40/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.40/1.52  
% 7.40/1.52  ------ Instantiation
% 7.40/1.52  
% 7.40/1.52  inst_num_of_clauses:                    3759
% 7.40/1.52  inst_num_in_passive:                    2466
% 7.40/1.52  inst_num_in_active:                     1293
% 7.40/1.52  inst_num_in_unprocessed:                0
% 7.40/1.52  inst_num_of_loops:                      1350
% 7.40/1.52  inst_num_of_learning_restarts:          0
% 7.40/1.52  inst_num_moves_active_passive:          56
% 7.40/1.52  inst_lit_activity:                      0
% 7.40/1.52  inst_lit_activity_moves:                3
% 7.40/1.52  inst_num_tautologies:                   0
% 7.40/1.52  inst_num_prop_implied:                  0
% 7.40/1.52  inst_num_existing_simplified:           0
% 7.40/1.52  inst_num_eq_res_simplified:             0
% 7.40/1.52  inst_num_child_elim:                    0
% 7.40/1.52  inst_num_of_dismatching_blockings:      874
% 7.40/1.52  inst_num_of_non_proper_insts:           3113
% 7.40/1.52  inst_num_of_duplicates:                 0
% 7.40/1.52  inst_inst_num_from_inst_to_res:         0
% 7.40/1.52  inst_dismatching_checking_time:         0.
% 7.40/1.52  
% 7.40/1.52  ------ Resolution
% 7.40/1.52  
% 7.40/1.52  res_num_of_clauses:                     0
% 7.40/1.52  res_num_in_passive:                     0
% 7.40/1.52  res_num_in_active:                      0
% 7.40/1.52  res_num_of_loops:                       135
% 7.40/1.52  res_forward_subset_subsumed:            34
% 7.40/1.52  res_backward_subset_subsumed:           0
% 7.40/1.52  res_forward_subsumed:                   0
% 7.40/1.52  res_backward_subsumed:                  0
% 7.40/1.52  res_forward_subsumption_resolution:     0
% 7.40/1.52  res_backward_subsumption_resolution:    0
% 7.40/1.52  res_clause_to_clause_subsumption:       2878
% 7.40/1.52  res_orphan_elimination:                 0
% 7.40/1.52  res_tautology_del:                      28
% 7.40/1.52  res_num_eq_res_simplified:              0
% 7.40/1.52  res_num_sel_changes:                    0
% 7.40/1.52  res_moves_from_active_to_pass:          0
% 7.40/1.52  
% 7.40/1.52  ------ Superposition
% 7.40/1.52  
% 7.40/1.52  sup_time_total:                         0.
% 7.40/1.52  sup_time_generating:                    0.
% 7.40/1.52  sup_time_sim_full:                      0.
% 7.40/1.52  sup_time_sim_immed:                     0.
% 7.40/1.52  
% 7.40/1.52  sup_num_of_clauses:                     942
% 7.40/1.52  sup_num_in_active:                      213
% 7.40/1.52  sup_num_in_passive:                     729
% 7.40/1.52  sup_num_of_loops:                       269
% 7.40/1.52  sup_fw_superposition:                   780
% 7.40/1.52  sup_bw_superposition:                   757
% 7.40/1.52  sup_immediate_simplified:               434
% 7.40/1.52  sup_given_eliminated:                   0
% 7.40/1.52  comparisons_done:                       0
% 7.40/1.52  comparisons_avoided:                    0
% 7.40/1.52  
% 7.40/1.52  ------ Simplifications
% 7.40/1.52  
% 7.40/1.52  
% 7.40/1.52  sim_fw_subset_subsumed:                 49
% 7.40/1.52  sim_bw_subset_subsumed:                 26
% 7.40/1.52  sim_fw_subsumed:                        50
% 7.40/1.52  sim_bw_subsumed:                        0
% 7.40/1.52  sim_fw_subsumption_res:                 2
% 7.40/1.52  sim_bw_subsumption_res:                 0
% 7.40/1.52  sim_tautology_del:                      4
% 7.40/1.52  sim_eq_tautology_del:                   128
% 7.40/1.52  sim_eq_res_simp:                        0
% 7.40/1.52  sim_fw_demodulated:                     1
% 7.40/1.52  sim_bw_demodulated:                     60
% 7.40/1.52  sim_light_normalised:                   351
% 7.40/1.52  sim_joinable_taut:                      0
% 7.40/1.52  sim_joinable_simp:                      0
% 7.40/1.52  sim_ac_normalised:                      0
% 7.40/1.52  sim_smt_subsumption:                    0
% 7.40/1.52  
%------------------------------------------------------------------------------
