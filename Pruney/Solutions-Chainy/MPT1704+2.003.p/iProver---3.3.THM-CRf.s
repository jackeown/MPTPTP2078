%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:42 EST 2020

% Result     : Theorem 15.14s
% Output     : CNFRefutation 15.14s
% Verified   : 
% Statistics : Number of formulae       :  314 (4750 expanded)
%              Number of clauses        :  203 (1200 expanded)
%              Number of leaves         :   30 (1225 expanded)
%              Depth                    :   32
%              Number of atoms          : 1239 (43405 expanded)
%              Number of equality atoms :  487 (5255 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_borsuk_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_borsuk_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_borsuk_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK3,X0)
          | ~ v1_borsuk_1(sK3,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
        & ( ( m1_pre_topc(sK3,X0)
            & v1_borsuk_1(sK3,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK3
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | ~ m1_pre_topc(sK2,X0)
              | ~ v1_borsuk_1(sK2,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
              | ( m1_pre_topc(sK2,X0)
                & v1_borsuk_1(sK2,X0) ) )
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK1)
                | ~ v1_borsuk_1(X2,sK1)
                | ~ m1_pre_topc(X1,sK1)
                | ~ v1_borsuk_1(X1,sK1) )
              & ( ( m1_pre_topc(X2,sK1)
                  & v1_borsuk_1(X2,sK1) )
                | ( m1_pre_topc(X1,sK1)
                  & v1_borsuk_1(X1,sK1) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ( ~ m1_pre_topc(sK3,sK1)
      | ~ v1_borsuk_1(sK3,sK1)
      | ~ m1_pre_topc(sK2,sK1)
      | ~ v1_borsuk_1(sK2,sK1) )
    & ( ( m1_pre_topc(sK3,sK1)
        & v1_borsuk_1(sK3,sK1) )
      | ( m1_pre_topc(sK2,sK1)
        & v1_borsuk_1(sK2,sK1) ) )
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f63,f66,f65,f64])).

fof(f110,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f67])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f116,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f80,f76])).

fof(f117,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f77,f116])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f118,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f78,f116])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f106,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f107,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f122,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,
    ( v1_borsuk_1(sK3,sK1)
    | m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f105,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f114,plain,
    ( m1_pre_topc(sK3,sK1)
    | m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f127,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f86,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f115,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v1_borsuk_1(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_borsuk_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f111,plain,
    ( v1_borsuk_1(sK3,sK1)
    | v1_borsuk_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_8,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_9,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2354,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2346,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6072,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_2346])).

cnf(c_26416,plain,
    ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_6072])).

cnf(c_26740,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_26416])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_48,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_49,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_51,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2352,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2349,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4361,plain,
    ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_2349])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_573,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_574,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_575,plain,
    ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_2577,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2579,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2577])).

cnf(c_8406,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v4_pre_topc(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4361,c_575,c_2579])).

cnf(c_8407,plain,
    ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8406])).

cnf(c_24,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2339,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4376,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2339])).

cnf(c_4572,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4376,c_48,c_49])).

cnf(c_4579,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) != iProver_top
    | v4_pre_topc(k1_xboole_0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_4572])).

cnf(c_8410,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8407,c_4579])).

cnf(c_26,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2337,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) = iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4030,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2337])).

cnf(c_4119,plain,
    ( v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4030,c_2579])).

cnf(c_4120,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4119])).

cnf(c_3008,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2354])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2345,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5737,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2345])).

cnf(c_6093,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5737,c_48,c_49])).

cnf(c_6102,plain,
    ( v3_pre_topc(X0,sK2) = iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_6093])).

cnf(c_6209,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3008,c_6102])).

cnf(c_8599,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4120,c_6209])).

cnf(c_30,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_33,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_262,plain,
    ( v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_borsuk_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_33])).

cnf(c_263,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_2322,plain,
    ( v1_borsuk_1(X0,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_21,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2342,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5246,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2342])).

cnf(c_5459,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5246,c_48,c_49])).

cnf(c_5466,plain,
    ( v1_borsuk_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_5459])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_50,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1327,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2667,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_1327,c_39])).

cnf(c_2668,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2667])).

cnf(c_1328,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2923,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_1328,c_39])).

cnf(c_2924,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2923])).

cnf(c_23555,plain,
    ( v1_borsuk_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5466,c_50,c_51,c_2668,c_2924])).

cnf(c_23562,plain,
    ( v1_borsuk_1(X0,sK3) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_23555])).

cnf(c_23568,plain,
    ( v1_borsuk_1(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_23562])).

cnf(c_23735,plain,
    ( v1_borsuk_1(sK3,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3008,c_23568])).

cnf(c_23,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2340,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4760,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2340])).

cnf(c_4943,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4760,c_48,c_49])).

cnf(c_4950,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_4943])).

cnf(c_22,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2341,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4928,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2341])).

cnf(c_5053,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4928,c_48,c_49])).

cnf(c_5061,plain,
    ( v4_pre_topc(X0,sK2) = iProver_top
    | v4_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_5053])).

cnf(c_5070,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_5061])).

cnf(c_6078,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2346])).

cnf(c_6217,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6078,c_48,c_49])).

cnf(c_6226,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_6217])).

cnf(c_6306,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),sK3) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_6226])).

cnf(c_15917,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_6306])).

cnf(c_16017,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2337,c_15917])).

cnf(c_23849,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23735,c_48,c_49,c_51,c_4950,c_5070,c_8410,c_16017])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2343,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4589,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2343])).

cnf(c_4743,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4589,c_48,c_49])).

cnf(c_23864,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_23849,c_4743])).

cnf(c_26919,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26740,c_48,c_49,c_51,c_8410,c_8599,c_23864])).

cnf(c_26923,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_26919])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2351,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_27133,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_26923,c_2351])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2355,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_29335,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_27133,c_2355])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2360,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_29344,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_29335,c_2360])).

cnf(c_50127,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_29344])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2344,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5219,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2344])).

cnf(c_5442,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5219,c_48,c_49])).

cnf(c_5448,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_5442])).

cnf(c_13586,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5448,c_2351])).

cnf(c_41824,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13586,c_2355])).

cnf(c_42027,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_41824])).

cnf(c_5467,plain,
    ( v4_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_5459])).

cnf(c_5721,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_5467])).

cnf(c_4661,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(X0))
    | r1_tarski(u1_struct_0(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8132,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4661])).

cnf(c_22705,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8132])).

cnf(c_22708,plain,
    ( r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22705])).

cnf(c_41823,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_13586])).

cnf(c_42023,plain,
    ( v4_pre_topc(k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2337,c_41823])).

cnf(c_42243,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42027,c_48,c_49,c_5070,c_5721,c_8410,c_22708,c_42023])).

cnf(c_26924,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_26919])).

cnf(c_26968,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_26924,c_2351])).

cnf(c_27244,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_26968,c_2355])).

cnf(c_27847,plain,
    ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK3),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_27244,c_2360])).

cnf(c_34548,plain,
    ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_27847])).

cnf(c_42251,plain,
    ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_42243,c_34548])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2353,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_42478,plain,
    ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_42251,c_2353])).

cnf(c_42481,plain,
    ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_42478,c_2353])).

cnf(c_3428,plain,
    ( r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_2351])).

cnf(c_122,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_125,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2622,plain,
    ( ~ m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
    | r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2623,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2622])).

cnf(c_7452,plain,
    ( r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3428,c_122,c_125,c_2623])).

cnf(c_7459,plain,
    ( r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7452,c_2355])).

cnf(c_42727,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42481,c_7459])).

cnf(c_50336,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50127,c_42727])).

cnf(c_50340,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_50336,c_2353])).

cnf(c_29,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_269,plain,
    ( ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_borsuk_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_33])).

cnf(c_270,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_2321,plain,
    ( v1_borsuk_1(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_50427,plain,
    ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_50340,c_2321])).

cnf(c_50616,plain,
    ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50427])).

cnf(c_50426,plain,
    ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_50340,c_2322])).

cnf(c_50613,plain,
    ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50426])).

cnf(c_1333,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v1_borsuk_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6001,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2)
    | X1 != X2
    | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_10802,plain,
    ( ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
    | v1_borsuk_1(sK3,X1)
    | X1 != X0
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_6001])).

cnf(c_10803,plain,
    ( X0 != X1
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1) != iProver_top
    | v1_borsuk_1(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10802])).

cnf(c_10805,plain,
    ( sK1 != sK1
    | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
    | v1_borsuk_1(sK3,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10803])).

cnf(c_1318,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3247,plain,
    ( X0 != X1
    | X0 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_4888,plain,
    ( X0 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | X0 != sK3
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_3247])).

cnf(c_6014,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4888])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2336,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3887,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2336])).

cnf(c_3891,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3887])).

cnf(c_2759,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v1_borsuk_1(sK3,sK1)
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_3844,plain,
    ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
    | ~ v1_borsuk_1(sK3,sK1)
    | X0 != sK1
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2759])).

cnf(c_3845,plain,
    ( X0 != sK1
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) = iProver_top
    | v1_borsuk_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3844])).

cnf(c_3847,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | sK1 != sK1
    | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | v1_borsuk_1(sK3,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3845])).

cnf(c_37,negated_conjecture,
    ( v1_borsuk_1(sK3,sK1)
    | m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2331,plain,
    ( v1_borsuk_1(sK3,sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_47,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK2,sK1)
    | m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_55,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_16,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_250,plain,
    ( ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_16])).

cnf(c_251,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_2323,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2547,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_15,c_251])).

cnf(c_2548,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2547])).

cnf(c_2638,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | m1_pre_topc(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2323,c_2548])).

cnf(c_2639,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2638])).

cnf(c_2642,plain,
    ( m1_pre_topc(sK2,X0) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_2639])).

cnf(c_2644,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2642])).

cnf(c_3130,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2331,c_47,c_48,c_49,c_55,c_2644])).

cnf(c_1317,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2995,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_2715,plain,
    ( v1_borsuk_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_2716,plain,
    ( v1_borsuk_1(sK2,sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2715])).

cnf(c_2526,plain,
    ( ~ v1_borsuk_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v4_pre_topc(u1_struct_0(sK2),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_2527,plain,
    ( v1_borsuk_1(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v4_pre_topc(u1_struct_0(sK2),sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2526])).

cnf(c_2501,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2502,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2501])).

cnf(c_146,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_142,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_34,negated_conjecture,
    ( ~ v1_borsuk_1(sK2,sK1)
    | ~ v1_borsuk_1(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_56,plain,
    ( v1_borsuk_1(sK2,sK1) != iProver_top
    | v1_borsuk_1(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,negated_conjecture,
    ( v1_borsuk_1(sK2,sK1)
    | v1_borsuk_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_52,plain,
    ( v1_borsuk_1(sK2,sK1) = iProver_top
    | v1_borsuk_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50616,c_50613,c_10805,c_6014,c_3891,c_3847,c_3130,c_2995,c_2716,c_2527,c_2502,c_146,c_142,c_56,c_52,c_39,c_47,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:07:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.14/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.14/2.49  
% 15.14/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.14/2.49  
% 15.14/2.49  ------  iProver source info
% 15.14/2.49  
% 15.14/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.14/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.14/2.49  git: non_committed_changes: false
% 15.14/2.49  git: last_make_outside_of_git: false
% 15.14/2.49  
% 15.14/2.49  ------ 
% 15.14/2.49  ------ Parsing...
% 15.14/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.14/2.49  
% 15.14/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.14/2.49  
% 15.14/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.14/2.49  
% 15.14/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.14/2.49  ------ Proving...
% 15.14/2.49  ------ Problem Properties 
% 15.14/2.49  
% 15.14/2.49  
% 15.14/2.49  clauses                                 43
% 15.14/2.49  conjectures                             12
% 15.14/2.49  EPR                                     16
% 15.14/2.49  Horn                                    37
% 15.14/2.49  unary                                   13
% 15.14/2.49  binary                                  6
% 15.14/2.49  lits                                    125
% 15.14/2.49  lits eq                                 5
% 15.14/2.49  fd_pure                                 0
% 15.14/2.49  fd_pseudo                               0
% 15.14/2.49  fd_cond                                 0
% 15.14/2.49  fd_pseudo_cond                          3
% 15.14/2.49  AC symbols                              0
% 15.14/2.49  
% 15.14/2.49  ------ Input Options Time Limit: Unbounded
% 15.14/2.49  
% 15.14/2.49  
% 15.14/2.49  ------ 
% 15.14/2.49  Current options:
% 15.14/2.49  ------ 
% 15.14/2.49  
% 15.14/2.49  
% 15.14/2.49  
% 15.14/2.49  
% 15.14/2.49  ------ Proving...
% 15.14/2.49  
% 15.14/2.49  
% 15.14/2.49  % SZS status Theorem for theBenchmark.p
% 15.14/2.49  
% 15.14/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.14/2.49  
% 15.14/2.49  fof(f22,conjecture,(
% 15.14/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f23,negated_conjecture,(
% 15.14/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 15.14/2.49    inference(negated_conjecture,[],[f22])).
% 15.14/2.49  
% 15.14/2.49  fof(f46,plain,(
% 15.14/2.49    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.14/2.49    inference(ennf_transformation,[],[f23])).
% 15.14/2.49  
% 15.14/2.49  fof(f47,plain,(
% 15.14/2.49    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f46])).
% 15.14/2.49  
% 15.14/2.49  fof(f62,plain,(
% 15.14/2.49    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.14/2.49    inference(nnf_transformation,[],[f47])).
% 15.14/2.49  
% 15.14/2.49  fof(f63,plain,(
% 15.14/2.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f62])).
% 15.14/2.49  
% 15.14/2.49  fof(f66,plain,(
% 15.14/2.49    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK3,X0) | ~v1_borsuk_1(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(sK3,X0) & v1_borsuk_1(sK3,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK3 & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 15.14/2.49    introduced(choice_axiom,[])).
% 15.14/2.49  
% 15.14/2.49  fof(f65,plain,(
% 15.14/2.49    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(sK2,X0) | ~v1_borsuk_1(sK2,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(sK2,X0) & v1_borsuk_1(sK2,X0))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 15.14/2.49    introduced(choice_axiom,[])).
% 15.14/2.49  
% 15.14/2.49  fof(f64,plain,(
% 15.14/2.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK1) | ~v1_borsuk_1(X2,sK1) | ~m1_pre_topc(X1,sK1) | ~v1_borsuk_1(X1,sK1)) & ((m1_pre_topc(X2,sK1) & v1_borsuk_1(X2,sK1)) | (m1_pre_topc(X1,sK1) & v1_borsuk_1(X1,sK1))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 15.14/2.49    introduced(choice_axiom,[])).
% 15.14/2.49  
% 15.14/2.49  fof(f67,plain,(
% 15.14/2.49    (((~m1_pre_topc(sK3,sK1) | ~v1_borsuk_1(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_borsuk_1(sK2,sK1)) & ((m1_pre_topc(sK3,sK1) & v1_borsuk_1(sK3,sK1)) | (m1_pre_topc(sK2,sK1) & v1_borsuk_1(sK2,sK1))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 15.14/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f63,f66,f65,f64])).
% 15.14/2.49  
% 15.14/2.49  fof(f110,plain,(
% 15.14/2.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f5,axiom,(
% 15.14/2.49    ! [X0] : k2_subset_1(X0) = X0),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f77,plain,(
% 15.14/2.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.14/2.49    inference(cnf_transformation,[],[f5])).
% 15.14/2.49  
% 15.14/2.49  fof(f8,axiom,(
% 15.14/2.49    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f80,plain,(
% 15.14/2.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 15.14/2.49    inference(cnf_transformation,[],[f8])).
% 15.14/2.49  
% 15.14/2.49  fof(f4,axiom,(
% 15.14/2.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f76,plain,(
% 15.14/2.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f4])).
% 15.14/2.49  
% 15.14/2.49  fof(f116,plain,(
% 15.14/2.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 15.14/2.49    inference(definition_unfolding,[],[f80,f76])).
% 15.14/2.49  
% 15.14/2.49  fof(f117,plain,(
% 15.14/2.49    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 15.14/2.49    inference(definition_unfolding,[],[f77,f116])).
% 15.14/2.49  
% 15.14/2.49  fof(f6,axiom,(
% 15.14/2.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f78,plain,(
% 15.14/2.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.14/2.49    inference(cnf_transformation,[],[f6])).
% 15.14/2.49  
% 15.14/2.49  fof(f118,plain,(
% 15.14/2.49    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 15.14/2.49    inference(definition_unfolding,[],[f78,f116])).
% 15.14/2.49  
% 15.14/2.49  fof(f15,axiom,(
% 15.14/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f35,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.14/2.49    inference(ennf_transformation,[],[f15])).
% 15.14/2.49  
% 15.14/2.49  fof(f36,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f35])).
% 15.14/2.49  
% 15.14/2.49  fof(f54,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(nnf_transformation,[],[f36])).
% 15.14/2.49  
% 15.14/2.49  fof(f55,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f54])).
% 15.14/2.49  
% 15.14/2.49  fof(f90,plain,(
% 15.14/2.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f55])).
% 15.14/2.49  
% 15.14/2.49  fof(f106,plain,(
% 15.14/2.49    v2_pre_topc(sK2)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f107,plain,(
% 15.14/2.49    l1_pre_topc(sK2)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f109,plain,(
% 15.14/2.49    l1_pre_topc(sK3)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f9,axiom,(
% 15.14/2.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f81,plain,(
% 15.14/2.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.14/2.49    inference(cnf_transformation,[],[f9])).
% 15.14/2.49  
% 15.14/2.49  fof(f12,axiom,(
% 15.14/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f30,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.14/2.49    inference(ennf_transformation,[],[f12])).
% 15.14/2.49  
% 15.14/2.49  fof(f31,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f30])).
% 15.14/2.49  
% 15.14/2.49  fof(f84,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f31])).
% 15.14/2.49  
% 15.14/2.49  fof(f1,axiom,(
% 15.14/2.49    v1_xboole_0(k1_xboole_0)),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f68,plain,(
% 15.14/2.49    v1_xboole_0(k1_xboole_0)),
% 15.14/2.49    inference(cnf_transformation,[],[f1])).
% 15.14/2.49  
% 15.14/2.49  fof(f16,axiom,(
% 15.14/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f37,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.14/2.49    inference(ennf_transformation,[],[f16])).
% 15.14/2.49  
% 15.14/2.49  fof(f38,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f37])).
% 15.14/2.49  
% 15.14/2.49  fof(f56,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(nnf_transformation,[],[f38])).
% 15.14/2.49  
% 15.14/2.49  fof(f57,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f56])).
% 15.14/2.49  
% 15.14/2.49  fof(f91,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f57])).
% 15.14/2.49  
% 15.14/2.49  fof(f17,axiom,(
% 15.14/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f39,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(ennf_transformation,[],[f17])).
% 15.14/2.49  
% 15.14/2.49  fof(f58,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(nnf_transformation,[],[f39])).
% 15.14/2.49  
% 15.14/2.49  fof(f95,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f58])).
% 15.14/2.49  
% 15.14/2.49  fof(f89,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f55])).
% 15.14/2.49  
% 15.14/2.49  fof(f19,axiom,(
% 15.14/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f41,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.14/2.49    inference(ennf_transformation,[],[f19])).
% 15.14/2.49  
% 15.14/2.49  fof(f42,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f41])).
% 15.14/2.49  
% 15.14/2.49  fof(f59,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(nnf_transformation,[],[f42])).
% 15.14/2.49  
% 15.14/2.49  fof(f60,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f59])).
% 15.14/2.49  
% 15.14/2.49  fof(f98,plain,(
% 15.14/2.49    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f60])).
% 15.14/2.49  
% 15.14/2.49  fof(f125,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(equality_resolution,[],[f98])).
% 15.14/2.49  
% 15.14/2.49  fof(f21,axiom,(
% 15.14/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f45,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(ennf_transformation,[],[f21])).
% 15.14/2.49  
% 15.14/2.49  fof(f103,plain,(
% 15.14/2.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f45])).
% 15.14/2.49  
% 15.14/2.49  fof(f94,plain,(
% 15.14/2.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f57])).
% 15.14/2.49  
% 15.14/2.49  fof(f108,plain,(
% 15.14/2.49    v2_pre_topc(sK3)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f92,plain,(
% 15.14/2.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f57])).
% 15.14/2.49  
% 15.14/2.49  fof(f93,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f57])).
% 15.14/2.49  
% 15.14/2.49  fof(f87,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f55])).
% 15.14/2.49  
% 15.14/2.49  fof(f10,axiom,(
% 15.14/2.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f26,plain,(
% 15.14/2.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 15.14/2.49    inference(ennf_transformation,[],[f10])).
% 15.14/2.49  
% 15.14/2.49  fof(f27,plain,(
% 15.14/2.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 15.14/2.49    inference(flattening,[],[f26])).
% 15.14/2.49  
% 15.14/2.49  fof(f82,plain,(
% 15.14/2.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f27])).
% 15.14/2.49  
% 15.14/2.49  fof(f3,axiom,(
% 15.14/2.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f50,plain,(
% 15.14/2.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.14/2.49    inference(nnf_transformation,[],[f3])).
% 15.14/2.49  
% 15.14/2.49  fof(f51,plain,(
% 15.14/2.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.14/2.49    inference(rectify,[],[f50])).
% 15.14/2.49  
% 15.14/2.49  fof(f52,plain,(
% 15.14/2.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 15.14/2.49    introduced(choice_axiom,[])).
% 15.14/2.49  
% 15.14/2.49  fof(f53,plain,(
% 15.14/2.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.14/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 15.14/2.49  
% 15.14/2.49  fof(f72,plain,(
% 15.14/2.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 15.14/2.49    inference(cnf_transformation,[],[f53])).
% 15.14/2.49  
% 15.14/2.49  fof(f122,plain,(
% 15.14/2.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 15.14/2.49    inference(equality_resolution,[],[f72])).
% 15.14/2.49  
% 15.14/2.49  fof(f2,axiom,(
% 15.14/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f48,plain,(
% 15.14/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.14/2.49    inference(nnf_transformation,[],[f2])).
% 15.14/2.49  
% 15.14/2.49  fof(f49,plain,(
% 15.14/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.14/2.49    inference(flattening,[],[f48])).
% 15.14/2.49  
% 15.14/2.49  fof(f71,plain,(
% 15.14/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f49])).
% 15.14/2.49  
% 15.14/2.49  fof(f88,plain,(
% 15.14/2.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f55])).
% 15.14/2.49  
% 15.14/2.49  fof(f7,axiom,(
% 15.14/2.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f79,plain,(
% 15.14/2.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 15.14/2.49    inference(cnf_transformation,[],[f7])).
% 15.14/2.49  
% 15.14/2.49  fof(f99,plain,(
% 15.14/2.49    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f60])).
% 15.14/2.49  
% 15.14/2.49  fof(f124,plain,(
% 15.14/2.49    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(equality_resolution,[],[f99])).
% 15.14/2.49  
% 15.14/2.49  fof(f18,axiom,(
% 15.14/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f25,plain,(
% 15.14/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 15.14/2.49    inference(pure_predicate_removal,[],[f18])).
% 15.14/2.49  
% 15.14/2.49  fof(f40,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(ennf_transformation,[],[f25])).
% 15.14/2.49  
% 15.14/2.49  fof(f97,plain,(
% 15.14/2.49    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f40])).
% 15.14/2.49  
% 15.14/2.49  fof(f112,plain,(
% 15.14/2.49    v1_borsuk_1(sK3,sK1) | m1_pre_topc(sK2,sK1)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f105,plain,(
% 15.14/2.49    l1_pre_topc(sK1)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f114,plain,(
% 15.14/2.49    m1_pre_topc(sK3,sK1) | m1_pre_topc(sK2,sK1)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f20,axiom,(
% 15.14/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f43,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(ennf_transformation,[],[f20])).
% 15.14/2.49  
% 15.14/2.49  fof(f44,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f43])).
% 15.14/2.49  
% 15.14/2.49  fof(f61,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(nnf_transformation,[],[f44])).
% 15.14/2.49  
% 15.14/2.49  fof(f101,plain,(
% 15.14/2.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f61])).
% 15.14/2.49  
% 15.14/2.49  fof(f127,plain,(
% 15.14/2.49    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 15.14/2.49    inference(equality_resolution,[],[f101])).
% 15.14/2.49  
% 15.14/2.49  fof(f14,axiom,(
% 15.14/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f24,plain,(
% 15.14/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 15.14/2.49    inference(pure_predicate_removal,[],[f14])).
% 15.14/2.49  
% 15.14/2.49  fof(f33,plain,(
% 15.14/2.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.14/2.49    inference(ennf_transformation,[],[f24])).
% 15.14/2.49  
% 15.14/2.49  fof(f34,plain,(
% 15.14/2.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.14/2.49    inference(flattening,[],[f33])).
% 15.14/2.49  
% 15.14/2.49  fof(f86,plain,(
% 15.14/2.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f34])).
% 15.14/2.49  
% 15.14/2.49  fof(f13,axiom,(
% 15.14/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.14/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.14/2.49  
% 15.14/2.49  fof(f32,plain,(
% 15.14/2.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.14/2.49    inference(ennf_transformation,[],[f13])).
% 15.14/2.49  
% 15.14/2.49  fof(f85,plain,(
% 15.14/2.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.14/2.49    inference(cnf_transformation,[],[f32])).
% 15.14/2.49  
% 15.14/2.49  fof(f69,plain,(
% 15.14/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.14/2.49    inference(cnf_transformation,[],[f49])).
% 15.14/2.49  
% 15.14/2.49  fof(f120,plain,(
% 15.14/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.14/2.49    inference(equality_resolution,[],[f69])).
% 15.14/2.49  
% 15.14/2.49  fof(f115,plain,(
% 15.14/2.49    ~m1_pre_topc(sK3,sK1) | ~v1_borsuk_1(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v1_borsuk_1(sK2,sK1)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f111,plain,(
% 15.14/2.49    v1_borsuk_1(sK3,sK1) | v1_borsuk_1(sK2,sK1)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  fof(f104,plain,(
% 15.14/2.49    v2_pre_topc(sK1)),
% 15.14/2.49    inference(cnf_transformation,[],[f67])).
% 15.14/2.49  
% 15.14/2.49  cnf(c_39,negated_conjecture,
% 15.14/2.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 15.14/2.49      inference(cnf_transformation,[],[f110]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_8,plain,
% 15.14/2.49      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 15.14/2.49      inference(cnf_transformation,[],[f117]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_9,plain,
% 15.14/2.49      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 15.14/2.49      inference(cnf_transformation,[],[f118]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2354,plain,
% 15.14/2.49      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_17,plain,
% 15.14/2.49      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2346,plain,
% 15.14/2.49      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6072,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.14/2.49      | m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2354,c_2346]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_26416,plain,
% 15.14/2.49      ( v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 15.14/2.49      | m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_6072]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_26740,plain,
% 15.14/2.49      ( v3_pre_topc(u1_struct_0(sK3),sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_26416]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_43,negated_conjecture,
% 15.14/2.49      ( v2_pre_topc(sK2) ),
% 15.14/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_48,plain,
% 15.14/2.49      ( v2_pre_topc(sK2) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42,negated_conjecture,
% 15.14/2.49      ( l1_pre_topc(sK2) ),
% 15.14/2.49      inference(cnf_transformation,[],[f107]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_49,plain,
% 15.14/2.49      ( l1_pre_topc(sK2) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_40,negated_conjecture,
% 15.14/2.49      ( l1_pre_topc(sK3) ),
% 15.14/2.49      inference(cnf_transformation,[],[f109]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_51,plain,
% 15.14/2.49      ( l1_pre_topc(sK3) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_11,plain,
% 15.14/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.14/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2352,plain,
% 15.14/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_14,plain,
% 15.14/2.49      ( v4_pre_topc(X0,X1)
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1)
% 15.14/2.49      | ~ v1_xboole_0(X0) ),
% 15.14/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2349,plain,
% 15.14/2.49      ( v4_pre_topc(X0,X1) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top
% 15.14/2.49      | v1_xboole_0(X0) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4361,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top
% 15.14/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2352,c_2349]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_0,plain,
% 15.14/2.49      ( v1_xboole_0(k1_xboole_0) ),
% 15.14/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_573,plain,
% 15.14/2.49      ( v4_pre_topc(X0,X1)
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1)
% 15.14/2.49      | k1_xboole_0 != X0 ),
% 15.14/2.49      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_574,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,X0)
% 15.14/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 15.14/2.49      | ~ v2_pre_topc(X0)
% 15.14/2.49      | ~ l1_pre_topc(X0) ),
% 15.14/2.49      inference(unflattening,[status(thm)],[c_573]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_575,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
% 15.14/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2577,plain,
% 15.14/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_11]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2579,plain,
% 15.14/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2577]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_8406,plain,
% 15.14/2.49      ( l1_pre_topc(X0) != iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | v4_pre_topc(k1_xboole_0,X0) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_4361,c_575,c_2579]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_8407,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(renaming,[status(thm)],[c_8406]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_24,plain,
% 15.14/2.49      ( ~ v4_pre_topc(X0,X1)
% 15.14/2.49      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f91]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2339,plain,
% 15.14/2.49      ( v4_pre_topc(X0,X1) != iProver_top
% 15.14/2.49      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4376,plain,
% 15.14/2.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | v4_pre_topc(X0,sK3) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2339]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4572,plain,
% 15.14/2.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | v4_pre_topc(X0,sK3) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_4376,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4579,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,sK2) != iProver_top
% 15.14/2.49      | v4_pre_topc(k1_xboole_0,sK3) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2352,c_4572]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_8410,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,sK3) = iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8407,c_4579]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_26,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 15.14/2.49      | ~ v4_pre_topc(X1,X0)
% 15.14/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.14/2.49      | ~ l1_pre_topc(X0) ),
% 15.14/2.49      inference(cnf_transformation,[],[f95]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2337,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) = iProver_top
% 15.14/2.49      | v4_pre_topc(X1,X0) != iProver_top
% 15.14/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4030,plain,
% 15.14/2.49      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 15.14/2.49      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 15.14/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_2337]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4119,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 15.14/2.49      | v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_4030,c_2579]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4120,plain,
% 15.14/2.49      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 15.14/2.49      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(renaming,[status(thm)],[c_4119]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3008,plain,
% 15.14/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_2354]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_18,plain,
% 15.14/2.49      ( v3_pre_topc(X0,X1)
% 15.14/2.49      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2345,plain,
% 15.14/2.49      ( v3_pre_topc(X0,X1) = iProver_top
% 15.14/2.49      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5737,plain,
% 15.14/2.49      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | v3_pre_topc(X0,sK2) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2345]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6093,plain,
% 15.14/2.49      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | v3_pre_topc(X0,sK2) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_5737,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6102,plain,
% 15.14/2.49      ( v3_pre_topc(X0,sK2) = iProver_top
% 15.14/2.49      | v3_pre_topc(X0,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_6093]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6209,plain,
% 15.14/2.49      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 15.14/2.49      | v3_pre_topc(u1_struct_0(sK3),sK3) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_3008,c_6102]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_8599,plain,
% 15.14/2.49      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 15.14/2.49      | v4_pre_topc(k1_xboole_0,sK3) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK3) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_4120,c_6209]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_30,plain,
% 15.14/2.49      ( ~ v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | v4_pre_topc(u1_struct_0(X0),X1)
% 15.14/2.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f125]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_33,plain,
% 15.14/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f103]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_262,plain,
% 15.14/2.49      ( v4_pre_topc(u1_struct_0(X0),X1)
% 15.14/2.49      | ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | ~ v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_30,c_33]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_263,plain,
% 15.14/2.49      ( ~ v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | v4_pre_topc(u1_struct_0(X0),X1)
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(renaming,[status(thm)],[c_262]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2322,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,X1) != iProver_top
% 15.14/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_21,plain,
% 15.14/2.49      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f94]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2342,plain,
% 15.14/2.49      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5246,plain,
% 15.14/2.49      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2342]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5459,plain,
% 15.14/2.49      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_5246,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5466,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.14/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2322,c_5459]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_41,negated_conjecture,
% 15.14/2.49      ( v2_pre_topc(sK3) ),
% 15.14/2.49      inference(cnf_transformation,[],[f108]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50,plain,
% 15.14/2.49      ( v2_pre_topc(sK3) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_1327,plain,
% 15.14/2.49      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 15.14/2.49      theory(equality) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2667,plain,
% 15.14/2.49      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 15.14/2.49      | ~ l1_pre_topc(sK3) ),
% 15.14/2.49      inference(resolution,[status(thm)],[c_1327,c_39]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2668,plain,
% 15.14/2.49      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 15.14/2.49      | l1_pre_topc(sK3) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2667]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_1328,plain,
% 15.14/2.49      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 15.14/2.49      theory(equality) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2923,plain,
% 15.14/2.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 15.14/2.49      | ~ v2_pre_topc(sK3) ),
% 15.14/2.49      inference(resolution,[status(thm)],[c_1328,c_39]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2924,plain,
% 15.14/2.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 15.14/2.49      | v2_pre_topc(sK3) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2923]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_23555,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_5466,c_50,c_51,c_2668,c_2924]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_23562,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,sK3) != iProver_top
% 15.14/2.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_23555]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_23568,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,sK3) != iProver_top
% 15.14/2.49      | m1_pre_topc(X0,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_23562]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_23735,plain,
% 15.14/2.49      ( v1_borsuk_1(sK3,sK3) != iProver_top
% 15.14/2.49      | m1_pre_topc(sK3,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_3008,c_23568]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_23,plain,
% 15.14/2.49      ( ~ v4_pre_topc(X0,X1)
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2340,plain,
% 15.14/2.49      ( v4_pre_topc(X0,X1) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4760,plain,
% 15.14/2.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2340]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4943,plain,
% 15.14/2.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_4760,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4950,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,sK2) != iProver_top
% 15.14/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2352,c_4943]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_22,plain,
% 15.14/2.49      ( v4_pre_topc(X0,X1)
% 15.14/2.49      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f93]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2341,plain,
% 15.14/2.49      ( v4_pre_topc(X0,X1) = iProver_top
% 15.14/2.49      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4928,plain,
% 15.14/2.49      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | v4_pre_topc(X0,sK2) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2341]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5053,plain,
% 15.14/2.49      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | v4_pre_topc(X0,sK2) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_4928,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5061,plain,
% 15.14/2.49      ( v4_pre_topc(X0,sK2) = iProver_top
% 15.14/2.49      | v4_pre_topc(X0,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_5053]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5070,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,sK2) = iProver_top
% 15.14/2.49      | v4_pre_topc(k1_xboole_0,sK3) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2352,c_5061]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6078,plain,
% 15.14/2.49      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2346]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6217,plain,
% 15.14/2.49      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_6078,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6226,plain,
% 15.14/2.49      ( v3_pre_topc(X0,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_6217]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6306,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2354,c_6226]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_15917,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_6306]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_16017,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK3) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2337,c_15917]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_23849,plain,
% 15.14/2.49      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_23735,c_48,c_49,c_51,c_4950,c_5070,c_8410,c_16017]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_20,plain,
% 15.14/2.49      ( ~ v3_pre_topc(X0,X1)
% 15.14/2.49      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2343,plain,
% 15.14/2.49      ( v3_pre_topc(X0,X1) != iProver_top
% 15.14/2.49      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4589,plain,
% 15.14/2.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | v3_pre_topc(X0,sK3) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2343]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4743,plain,
% 15.14/2.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | v3_pre_topc(X0,sK3) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_4589,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_23864,plain,
% 15.14/2.49      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 15.14/2.49      | v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_23849,c_4743]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_26919,plain,
% 15.14/2.49      ( m1_subset_1(k3_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_26740,c_48,c_49,c_51,c_8410,c_8599,c_23864]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_26923,plain,
% 15.14/2.49      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_26919]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_12,plain,
% 15.14/2.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f82]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2351,plain,
% 15.14/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 15.14/2.49      | r2_hidden(X0,X1) = iProver_top
% 15.14/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_27133,plain,
% 15.14/2.49      ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_26923,c_2351]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_7,plain,
% 15.14/2.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f122]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2355,plain,
% 15.14/2.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.14/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_29335,plain,
% 15.14/2.49      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK2)) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_27133,c_2355]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_1,plain,
% 15.14/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.14/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2360,plain,
% 15.14/2.49      ( X0 = X1
% 15.14/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.14/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_29344,plain,
% 15.14/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_29335,c_2360]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50127,plain,
% 15.14/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_29344]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_19,plain,
% 15.14/2.49      ( ~ v3_pre_topc(X0,X1)
% 15.14/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2344,plain,
% 15.14/2.49      ( v3_pre_topc(X0,X1) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5219,plain,
% 15.14/2.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2344]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5442,plain,
% 15.14/2.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_5219,c_48,c_49]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5448,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
% 15.14/2.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2354,c_5442]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_13586,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
% 15.14/2.49      | r2_hidden(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_5448,c_2351]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_41824,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
% 15.14/2.49      | r1_tarski(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),u1_struct_0(sK3)) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_13586,c_2355]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42027,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_41824]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5467,plain,
% 15.14/2.49      ( v4_pre_topc(X0,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_5459]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_5721,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,sK3) != iProver_top
% 15.14/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2352,c_5467]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4661,plain,
% 15.14/2.49      ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(X0))
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),X0) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_8132,plain,
% 15.14/2.49      ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_4661]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_22705,plain,
% 15.14/2.49      ( ~ r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_8132]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_22708,plain,
% 15.14/2.49      ( r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_22705]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_41823,plain,
% 15.14/2.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) != iProver_top
% 15.14/2.49      | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_13586]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42023,plain,
% 15.14/2.49      ( v4_pre_topc(k1_xboole_0,sK2) != iProver_top
% 15.14/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.14/2.49      | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2337,c_41823]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42243,plain,
% 15.14/2.49      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_42027,c_48,c_49,c_5070,c_5721,c_8410,c_22708,c_42023]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_26924,plain,
% 15.14/2.49      ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_26919]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_26968,plain,
% 15.14/2.49      ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_26924,c_2351]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_27244,plain,
% 15.14/2.49      ( r1_tarski(k3_subset_1(u1_struct_0(sK3),k1_xboole_0),u1_struct_0(sK2)) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_26968,c_2355]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_27847,plain,
% 15.14/2.49      ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK3),k1_xboole_0)) != iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_27244,c_2360]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_34548,plain,
% 15.14/2.49      ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
% 15.14/2.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_8,c_27847]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42251,plain,
% 15.14/2.49      ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_42243,c_34548]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_10,plain,
% 15.14/2.49      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 15.14/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2353,plain,
% 15.14/2.49      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42478,plain,
% 15.14/2.49      ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2)
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_42251,c_2353]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42481,plain,
% 15.14/2.49      ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK2) ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_42478,c_2353]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3428,plain,
% 15.14/2.49      ( r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_2354,c_2351]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_122,plain,
% 15.14/2.49      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_125,plain,
% 15.14/2.49      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2622,plain,
% 15.14/2.49      ( ~ m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
% 15.14/2.49      | r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2623,plain,
% 15.14/2.49      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
% 15.14/2.49      | r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2622]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_7452,plain,
% 15.14/2.49      ( r2_hidden(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_3428,c_122,c_125,c_2623]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_7459,plain,
% 15.14/2.49      ( r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_7452,c_2355]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_42727,plain,
% 15.14/2.49      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_42481,c_7459]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50336,plain,
% 15.14/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
% 15.14/2.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_50127,c_42727]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50340,plain,
% 15.14/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_50336,c_2353]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_29,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 15.14/2.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f124]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_269,plain,
% 15.14/2.49      ( ~ v4_pre_topc(u1_struct_0(X0),X1)
% 15.14/2.49      | ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_29,c_33]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_270,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 15.14/2.49      | ~ v2_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(renaming,[status(thm)],[c_269]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2321,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,X1) = iProver_top
% 15.14/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 15.14/2.49      | v2_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50427,plain,
% 15.14/2.49      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) = iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(sK2),X0) != iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_50340,c_2321]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50616,plain,
% 15.14/2.49      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(sK2),sK1) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_50427]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50426,plain,
% 15.14/2.49      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(sK2),X0) = iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_50340,c_2322]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_50613,plain,
% 15.14/2.49      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(sK2),sK1) = iProver_top
% 15.14/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_50426]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_1333,plain,
% 15.14/2.49      ( ~ v1_borsuk_1(X0,X1) | v1_borsuk_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.14/2.49      theory(equality) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6001,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X2)
% 15.14/2.49      | X1 != X2
% 15.14/2.49      | X0 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_1333]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_10802,plain,
% 15.14/2.49      ( ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
% 15.14/2.49      | v1_borsuk_1(sK3,X1)
% 15.14/2.49      | X1 != X0
% 15.14/2.49      | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_6001]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_10803,plain,
% 15.14/2.49      ( X0 != X1
% 15.14/2.49      | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 15.14/2.49      | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1) != iProver_top
% 15.14/2.49      | v1_borsuk_1(sK3,X0) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_10802]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_10805,plain,
% 15.14/2.49      ( sK1 != sK1
% 15.14/2.49      | sK3 != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 15.14/2.49      | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) != iProver_top
% 15.14/2.49      | v1_borsuk_1(sK3,sK1) = iProver_top ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_10803]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_1318,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3247,plain,
% 15.14/2.49      ( X0 != X1
% 15.14/2.49      | X0 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 15.14/2.49      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X1 ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_1318]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_4888,plain,
% 15.14/2.49      ( X0 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 15.14/2.49      | X0 != sK3
% 15.14/2.49      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_3247]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_6014,plain,
% 15.14/2.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 15.14/2.49      | sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 15.14/2.49      | sK3 != sK3 ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_4888]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_27,plain,
% 15.14/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f97]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2336,plain,
% 15.14/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3887,plain,
% 15.14/2.49      ( m1_pre_topc(sK2,X0) != iProver_top
% 15.14/2.49      | m1_pre_topc(sK3,X0) = iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2336]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3891,plain,
% 15.14/2.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 15.14/2.49      | m1_pre_topc(sK3,sK1) = iProver_top
% 15.14/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_3887]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2759,plain,
% 15.14/2.49      ( v1_borsuk_1(X0,X1)
% 15.14/2.49      | ~ v1_borsuk_1(sK3,sK1)
% 15.14/2.49      | X1 != sK1
% 15.14/2.49      | X0 != sK3 ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_1333]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3844,plain,
% 15.14/2.49      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
% 15.14/2.49      | ~ v1_borsuk_1(sK3,sK1)
% 15.14/2.49      | X0 != sK1
% 15.14/2.49      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_2759]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3845,plain,
% 15.14/2.49      ( X0 != sK1
% 15.14/2.49      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 15.14/2.49      | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) = iProver_top
% 15.14/2.49      | v1_borsuk_1(sK3,sK1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_3844]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3847,plain,
% 15.14/2.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 15.14/2.49      | sK1 != sK1
% 15.14/2.49      | v1_borsuk_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 15.14/2.49      | v1_borsuk_1(sK3,sK1) != iProver_top ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_3845]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_37,negated_conjecture,
% 15.14/2.49      ( v1_borsuk_1(sK3,sK1) | m1_pre_topc(sK2,sK1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f112]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2331,plain,
% 15.14/2.49      ( v1_borsuk_1(sK3,sK1) = iProver_top
% 15.14/2.49      | m1_pre_topc(sK2,sK1) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_44,negated_conjecture,
% 15.14/2.49      ( l1_pre_topc(sK1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f105]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_47,plain,
% 15.14/2.49      ( l1_pre_topc(sK1) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_35,negated_conjecture,
% 15.14/2.49      ( m1_pre_topc(sK2,sK1) | m1_pre_topc(sK3,sK1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f114]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_55,plain,
% 15.14/2.49      ( m1_pre_topc(sK2,sK1) = iProver_top
% 15.14/2.49      | m1_pre_topc(sK3,sK1) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_32,plain,
% 15.14/2.49      ( m1_pre_topc(X0,X1)
% 15.14/2.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.14/2.49      | ~ v2_pre_topc(X0)
% 15.14/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.14/2.49      | ~ l1_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X0)
% 15.14/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.14/2.49      inference(cnf_transformation,[],[f127]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_16,plain,
% 15.14/2.49      ( ~ v2_pre_topc(X0)
% 15.14/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.14/2.49      | ~ l1_pre_topc(X0) ),
% 15.14/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_250,plain,
% 15.14/2.49      ( ~ v2_pre_topc(X0)
% 15.14/2.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.14/2.49      | m1_pre_topc(X0,X1)
% 15.14/2.49      | ~ l1_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(X0)
% 15.14/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_32,c_16]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_251,plain,
% 15.14/2.49      ( m1_pre_topc(X0,X1)
% 15.14/2.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.14/2.49      | ~ v2_pre_topc(X0)
% 15.14/2.49      | ~ l1_pre_topc(X0)
% 15.14/2.49      | ~ l1_pre_topc(X1)
% 15.14/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.14/2.49      inference(renaming,[status(thm)],[c_250]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2323,plain,
% 15.14/2.49      ( m1_pre_topc(X0,X1) = iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_15,plain,
% 15.14/2.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.14/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2547,plain,
% 15.14/2.49      ( m1_pre_topc(X0,X1)
% 15.14/2.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.14/2.49      | ~ v2_pre_topc(X0)
% 15.14/2.49      | ~ l1_pre_topc(X0)
% 15.14/2.49      | ~ l1_pre_topc(X1) ),
% 15.14/2.49      inference(backward_subsumption_resolution,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_15,c_251]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2548,plain,
% 15.14/2.49      ( m1_pre_topc(X0,X1) = iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2547]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2638,plain,
% 15.14/2.49      ( l1_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 15.14/2.49      | m1_pre_topc(X0,X1) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_2323,c_2548]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2639,plain,
% 15.14/2.49      ( m1_pre_topc(X0,X1) = iProver_top
% 15.14/2.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 15.14/2.49      | v2_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(X1) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.14/2.49      inference(renaming,[status(thm)],[c_2638]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2642,plain,
% 15.14/2.49      ( m1_pre_topc(sK2,X0) = iProver_top
% 15.14/2.49      | m1_pre_topc(sK3,X0) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(X0) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.14/2.49      inference(superposition,[status(thm)],[c_39,c_2639]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2644,plain,
% 15.14/2.49      ( m1_pre_topc(sK2,sK1) = iProver_top
% 15.14/2.49      | m1_pre_topc(sK3,sK1) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_2642]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3130,plain,
% 15.14/2.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 15.14/2.49      inference(global_propositional_subsumption,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_2331,c_47,c_48,c_49,c_55,c_2644]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_1317,plain,( X0 = X0 ),theory(equality) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2995,plain,
% 15.14/2.49      ( sK3 = sK3 ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_1317]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2715,plain,
% 15.14/2.49      ( v1_borsuk_1(sK2,sK1)
% 15.14/2.49      | ~ m1_pre_topc(sK2,sK1)
% 15.14/2.49      | ~ v4_pre_topc(u1_struct_0(sK2),sK1)
% 15.14/2.49      | ~ v2_pre_topc(sK1)
% 15.14/2.49      | ~ l1_pre_topc(sK1) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_270]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2716,plain,
% 15.14/2.49      ( v1_borsuk_1(sK2,sK1) = iProver_top
% 15.14/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(sK2),sK1) != iProver_top
% 15.14/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2715]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2526,plain,
% 15.14/2.49      ( ~ v1_borsuk_1(sK2,sK1)
% 15.14/2.49      | ~ m1_pre_topc(sK2,sK1)
% 15.14/2.49      | v4_pre_topc(u1_struct_0(sK2),sK1)
% 15.14/2.49      | ~ v2_pre_topc(sK1)
% 15.14/2.49      | ~ l1_pre_topc(sK1) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_263]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2527,plain,
% 15.14/2.49      ( v1_borsuk_1(sK2,sK1) != iProver_top
% 15.14/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.14/2.49      | v4_pre_topc(u1_struct_0(sK2),sK1) = iProver_top
% 15.14/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2526]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2501,plain,
% 15.14/2.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1)
% 15.14/2.49      | ~ m1_pre_topc(sK2,sK1)
% 15.14/2.49      | ~ l1_pre_topc(sK1) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_27]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_2502,plain,
% 15.14/2.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK1) = iProver_top
% 15.14/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.14/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_2501]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_146,plain,
% 15.14/2.49      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_3,plain,
% 15.14/2.49      ( r1_tarski(X0,X0) ),
% 15.14/2.49      inference(cnf_transformation,[],[f120]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_142,plain,
% 15.14/2.49      ( r1_tarski(sK1,sK1) ),
% 15.14/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_34,negated_conjecture,
% 15.14/2.49      ( ~ v1_borsuk_1(sK2,sK1)
% 15.14/2.49      | ~ v1_borsuk_1(sK3,sK1)
% 15.14/2.49      | ~ m1_pre_topc(sK2,sK1)
% 15.14/2.49      | ~ m1_pre_topc(sK3,sK1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f115]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_56,plain,
% 15.14/2.49      ( v1_borsuk_1(sK2,sK1) != iProver_top
% 15.14/2.49      | v1_borsuk_1(sK3,sK1) != iProver_top
% 15.14/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.14/2.49      | m1_pre_topc(sK3,sK1) != iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_38,negated_conjecture,
% 15.14/2.49      ( v1_borsuk_1(sK2,sK1) | v1_borsuk_1(sK3,sK1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f111]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_52,plain,
% 15.14/2.49      ( v1_borsuk_1(sK2,sK1) = iProver_top
% 15.14/2.49      | v1_borsuk_1(sK3,sK1) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_45,negated_conjecture,
% 15.14/2.49      ( v2_pre_topc(sK1) ),
% 15.14/2.49      inference(cnf_transformation,[],[f104]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(c_46,plain,
% 15.14/2.49      ( v2_pre_topc(sK1) = iProver_top ),
% 15.14/2.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 15.14/2.49  
% 15.14/2.49  cnf(contradiction,plain,
% 15.14/2.49      ( $false ),
% 15.14/2.49      inference(minisat,
% 15.14/2.49                [status(thm)],
% 15.14/2.49                [c_50616,c_50613,c_10805,c_6014,c_3891,c_3847,c_3130,
% 15.14/2.49                 c_2995,c_2716,c_2527,c_2502,c_146,c_142,c_56,c_52,c_39,
% 15.14/2.49                 c_47,c_46]) ).
% 15.14/2.49  
% 15.14/2.49  
% 15.14/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.14/2.49  
% 15.14/2.49  ------                               Statistics
% 15.14/2.49  
% 15.14/2.49  ------ Selected
% 15.14/2.49  
% 15.14/2.49  total_time:                             1.7
% 15.14/2.49  
%------------------------------------------------------------------------------
