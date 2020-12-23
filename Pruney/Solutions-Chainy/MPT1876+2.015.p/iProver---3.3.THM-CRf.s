%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:49 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  209 (2945 expanded)
%              Number of clauses        :  126 ( 782 expanded)
%              Number of leaves         :   21 ( 652 expanded)
%              Depth                    :   25
%              Number of atoms          :  795 (19707 expanded)
%              Number of equality atoms :  241 (1237 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).

fof(f73,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK5)
          | ~ v2_tex_2(sK5,X0) )
        & ( v1_zfmisc_1(sK5)
          | v2_tex_2(sK5,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK4) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ( ~ v1_zfmisc_1(sK5)
      | ~ v2_tex_2(sK5,sK4) )
    & ( v1_zfmisc_1(sK5)
      | v2_tex_2(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & ~ v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f68,f70,f69])).

fof(f107,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f71])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f106,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f103,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f105,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f108,plain,
    ( v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & v1_tdlat_3(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & v1_tdlat_3(sK3(X0,X1))
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f65])).

fof(f100,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f96,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f93,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f91,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f88,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f87,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f109,plain,
    ( ~ v1_zfmisc_1(sK5)
    | ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4033,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_4009,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4021,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5510,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_4021])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4019,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5566,plain,
    ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5510,c_4019])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_42,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4022,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4712,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_4022])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_290,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_358,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_291])).

cnf(c_4002,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_5057,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4712,c_4002])).

cnf(c_5675,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5566,c_42,c_5057])).

cnf(c_5676,plain,
    ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_5675])).

cnf(c_5683,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4033,c_5676])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4330,plain,
    ( r2_hidden(sK0(sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4331,plain,
    ( r2_hidden(sK0(sK5),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4330])).

cnf(c_4519,plain,
    ( m1_subset_1(sK0(sK5),X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4702,plain,
    ( m1_subset_1(sK0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_4519])).

cnf(c_4703,plain,
    ( m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4702])).

cnf(c_4846,plain,
    ( ~ m1_subset_1(sK0(sK5),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4852,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
    | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4846])).

cnf(c_5704,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5683,c_42,c_43,c_4331,c_4703,c_4852,c_5057])).

cnf(c_29,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4012,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5707,plain,
    ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5704,c_4012])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_38,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_39,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_41,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9407,plain,
    ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5707,c_38,c_39,c_41,c_42,c_43,c_4331,c_4703])).

cnf(c_31,negated_conjecture,
    ( v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4010,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4016,plain,
    ( u1_struct_0(sK3(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5975,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v2_tex_2(sK5,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_4016])).

cnf(c_6354,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5975,c_38,c_39,c_41,c_42])).

cnf(c_6360,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4010,c_6354])).

cnf(c_9,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4024,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4763,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_4022])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_208,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_11,c_10])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_4003,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_5271,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4763,c_4003])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_101,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6681,plain,
    ( v1_zfmisc_1(X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | k1_tarski(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5271,c_101])).

cnf(c_6682,plain,
    ( k1_tarski(X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6681])).

cnf(c_6690,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4033,c_6682])).

cnf(c_6812,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | k1_tarski(sK0(sK5)) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6360,c_6690])).

cnf(c_6834,plain,
    ( v1_xboole_0(sK5)
    | u1_struct_0(sK3(sK4,sK5)) = sK5
    | k1_tarski(sK0(sK5)) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6812])).

cnf(c_7035,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | u1_struct_0(sK3(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6812,c_33,c_6834])).

cnf(c_7036,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | k1_tarski(sK0(sK5)) = sK5 ),
    inference(renaming,[status(thm)],[c_7035])).

cnf(c_7040,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | v2_tex_2(k6_domain_1(sK5,X0),sK3(sK4,sK5)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3(sK4,sK5))) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | v2_pre_topc(sK3(sK4,sK5)) != iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7036,c_4012])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_19,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_214,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_19])).

cnf(c_215,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_16,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_488,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_14,c_16])).

cnf(c_506,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_215,c_488])).

cnf(c_4001,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_tdlat_3(X0) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_7041,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v1_zfmisc_1(sK5) = iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7036,c_4001])).

cnf(c_44,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK3(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_294,plain,
    ( v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_295,plain,
    ( v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_886,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK3(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_295])).

cnf(c_887,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_struct_0(sK3(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_889,plain,
    ( ~ v2_struct_0(sK3(sK4,sK5))
    | v1_zfmisc_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_37,c_36,c_34,c_33,c_32])).

cnf(c_891,plain,
    ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_27,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK3(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(sK3(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_295])).

cnf(c_901,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | v1_tdlat_3(sK3(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_903,plain,
    ( v1_tdlat_3(sK3(sK4,sK5))
    | v1_zfmisc_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_37,c_36,c_34,c_33,c_32])).

cnf(c_905,plain,
    ( v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_26,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK3(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4015,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK3(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6051,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_4015])).

cnf(c_6494,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6051,c_38,c_39,c_41,c_42])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4020,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6500,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_4020])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1150,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_1151,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1150])).

cnf(c_4000,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_6501,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v2_tdlat_3(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_4000])).

cnf(c_35,negated_conjecture,
    ( v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_40,plain,
    ( v2_tdlat_3(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6585,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6501,c_38,c_40,c_41])).

cnf(c_7241,plain,
    ( v1_zfmisc_1(sK5) = iProver_top
    | k1_tarski(sK0(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7041,c_38,c_40,c_41,c_44,c_891,c_905,c_6500,c_6501])).

cnf(c_7242,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_7241])).

cnf(c_7247,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7242,c_6690])).

cnf(c_7308,plain,
    ( k1_tarski(sK0(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7040,c_42,c_7247])).

cnf(c_9411,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9407,c_7308])).

cnf(c_9414,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_9411,c_6354])).

cnf(c_9544,plain,
    ( v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v1_zfmisc_1(sK5) = iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9414,c_4001])).

cnf(c_7311,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_7308,c_5704])).

cnf(c_7641,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7311,c_4012])).

cnf(c_4013,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5793,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_4013])).

cnf(c_6487,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5793,c_38,c_39,c_41,c_42])).

cnf(c_4014,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(sK3(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5869,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_4014])).

cnf(c_6266,plain,
    ( v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5869,c_38,c_39,c_41,c_42])).

cnf(c_6267,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6266])).

cnf(c_30,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_45,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v1_zfmisc_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9544,c_7641,c_6585,c_6500,c_6487,c_6267,c_4703,c_4331,c_45,c_43,c_42,c_41,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.07/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.02  
% 3.07/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/1.02  
% 3.07/1.02  ------  iProver source info
% 3.07/1.02  
% 3.07/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.07/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/1.02  git: non_committed_changes: false
% 3.07/1.02  git: last_make_outside_of_git: false
% 3.07/1.02  
% 3.07/1.02  ------ 
% 3.07/1.02  
% 3.07/1.02  ------ Input Options
% 3.07/1.02  
% 3.07/1.02  --out_options                           all
% 3.07/1.02  --tptp_safe_out                         true
% 3.07/1.02  --problem_path                          ""
% 3.07/1.02  --include_path                          ""
% 3.07/1.02  --clausifier                            res/vclausify_rel
% 3.07/1.02  --clausifier_options                    --mode clausify
% 3.07/1.02  --stdin                                 false
% 3.07/1.02  --stats_out                             all
% 3.07/1.02  
% 3.07/1.02  ------ General Options
% 3.07/1.02  
% 3.07/1.02  --fof                                   false
% 3.07/1.02  --time_out_real                         305.
% 3.07/1.02  --time_out_virtual                      -1.
% 3.07/1.02  --symbol_type_check                     false
% 3.07/1.02  --clausify_out                          false
% 3.07/1.02  --sig_cnt_out                           false
% 3.07/1.02  --trig_cnt_out                          false
% 3.07/1.02  --trig_cnt_out_tolerance                1.
% 3.07/1.02  --trig_cnt_out_sk_spl                   false
% 3.07/1.02  --abstr_cl_out                          false
% 3.07/1.02  
% 3.07/1.02  ------ Global Options
% 3.07/1.02  
% 3.07/1.02  --schedule                              default
% 3.07/1.02  --add_important_lit                     false
% 3.07/1.02  --prop_solver_per_cl                    1000
% 3.07/1.02  --min_unsat_core                        false
% 3.07/1.02  --soft_assumptions                      false
% 3.07/1.02  --soft_lemma_size                       3
% 3.07/1.02  --prop_impl_unit_size                   0
% 3.07/1.02  --prop_impl_unit                        []
% 3.07/1.02  --share_sel_clauses                     true
% 3.07/1.02  --reset_solvers                         false
% 3.07/1.02  --bc_imp_inh                            [conj_cone]
% 3.07/1.02  --conj_cone_tolerance                   3.
% 3.07/1.02  --extra_neg_conj                        none
% 3.07/1.02  --large_theory_mode                     true
% 3.07/1.02  --prolific_symb_bound                   200
% 3.07/1.02  --lt_threshold                          2000
% 3.07/1.02  --clause_weak_htbl                      true
% 3.07/1.02  --gc_record_bc_elim                     false
% 3.07/1.02  
% 3.07/1.02  ------ Preprocessing Options
% 3.07/1.02  
% 3.07/1.02  --preprocessing_flag                    true
% 3.07/1.02  --time_out_prep_mult                    0.1
% 3.07/1.02  --splitting_mode                        input
% 3.07/1.02  --splitting_grd                         true
% 3.07/1.02  --splitting_cvd                         false
% 3.07/1.02  --splitting_cvd_svl                     false
% 3.07/1.02  --splitting_nvd                         32
% 3.07/1.02  --sub_typing                            true
% 3.07/1.02  --prep_gs_sim                           true
% 3.07/1.02  --prep_unflatten                        true
% 3.07/1.02  --prep_res_sim                          true
% 3.07/1.02  --prep_upred                            true
% 3.07/1.02  --prep_sem_filter                       exhaustive
% 3.07/1.02  --prep_sem_filter_out                   false
% 3.07/1.02  --pred_elim                             true
% 3.07/1.02  --res_sim_input                         true
% 3.07/1.02  --eq_ax_congr_red                       true
% 3.07/1.02  --pure_diseq_elim                       true
% 3.07/1.02  --brand_transform                       false
% 3.07/1.02  --non_eq_to_eq                          false
% 3.07/1.02  --prep_def_merge                        true
% 3.07/1.02  --prep_def_merge_prop_impl              false
% 3.07/1.02  --prep_def_merge_mbd                    true
% 3.07/1.02  --prep_def_merge_tr_red                 false
% 3.07/1.02  --prep_def_merge_tr_cl                  false
% 3.07/1.02  --smt_preprocessing                     true
% 3.07/1.02  --smt_ac_axioms                         fast
% 3.07/1.02  --preprocessed_out                      false
% 3.07/1.02  --preprocessed_stats                    false
% 3.07/1.02  
% 3.07/1.02  ------ Abstraction refinement Options
% 3.07/1.02  
% 3.07/1.02  --abstr_ref                             []
% 3.07/1.02  --abstr_ref_prep                        false
% 3.07/1.02  --abstr_ref_until_sat                   false
% 3.07/1.02  --abstr_ref_sig_restrict                funpre
% 3.07/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.02  --abstr_ref_under                       []
% 3.07/1.02  
% 3.07/1.02  ------ SAT Options
% 3.07/1.02  
% 3.07/1.02  --sat_mode                              false
% 3.07/1.02  --sat_fm_restart_options                ""
% 3.07/1.02  --sat_gr_def                            false
% 3.07/1.02  --sat_epr_types                         true
% 3.07/1.02  --sat_non_cyclic_types                  false
% 3.07/1.02  --sat_finite_models                     false
% 3.07/1.02  --sat_fm_lemmas                         false
% 3.07/1.02  --sat_fm_prep                           false
% 3.07/1.02  --sat_fm_uc_incr                        true
% 3.07/1.02  --sat_out_model                         small
% 3.07/1.02  --sat_out_clauses                       false
% 3.07/1.02  
% 3.07/1.02  ------ QBF Options
% 3.07/1.02  
% 3.07/1.02  --qbf_mode                              false
% 3.07/1.02  --qbf_elim_univ                         false
% 3.07/1.02  --qbf_dom_inst                          none
% 3.07/1.02  --qbf_dom_pre_inst                      false
% 3.07/1.02  --qbf_sk_in                             false
% 3.07/1.02  --qbf_pred_elim                         true
% 3.07/1.02  --qbf_split                             512
% 3.07/1.02  
% 3.07/1.02  ------ BMC1 Options
% 3.07/1.02  
% 3.07/1.02  --bmc1_incremental                      false
% 3.07/1.02  --bmc1_axioms                           reachable_all
% 3.07/1.02  --bmc1_min_bound                        0
% 3.07/1.02  --bmc1_max_bound                        -1
% 3.07/1.02  --bmc1_max_bound_default                -1
% 3.07/1.02  --bmc1_symbol_reachability              true
% 3.07/1.02  --bmc1_property_lemmas                  false
% 3.07/1.02  --bmc1_k_induction                      false
% 3.07/1.02  --bmc1_non_equiv_states                 false
% 3.07/1.02  --bmc1_deadlock                         false
% 3.07/1.02  --bmc1_ucm                              false
% 3.07/1.02  --bmc1_add_unsat_core                   none
% 3.07/1.02  --bmc1_unsat_core_children              false
% 3.07/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.02  --bmc1_out_stat                         full
% 3.07/1.02  --bmc1_ground_init                      false
% 3.07/1.02  --bmc1_pre_inst_next_state              false
% 3.07/1.02  --bmc1_pre_inst_state                   false
% 3.07/1.02  --bmc1_pre_inst_reach_state             false
% 3.07/1.02  --bmc1_out_unsat_core                   false
% 3.07/1.02  --bmc1_aig_witness_out                  false
% 3.07/1.02  --bmc1_verbose                          false
% 3.07/1.02  --bmc1_dump_clauses_tptp                false
% 3.07/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.02  --bmc1_dump_file                        -
% 3.07/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.02  --bmc1_ucm_extend_mode                  1
% 3.07/1.02  --bmc1_ucm_init_mode                    2
% 3.07/1.02  --bmc1_ucm_cone_mode                    none
% 3.07/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.02  --bmc1_ucm_relax_model                  4
% 3.07/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.02  --bmc1_ucm_layered_model                none
% 3.07/1.02  --bmc1_ucm_max_lemma_size               10
% 3.07/1.02  
% 3.07/1.02  ------ AIG Options
% 3.07/1.02  
% 3.07/1.02  --aig_mode                              false
% 3.07/1.02  
% 3.07/1.02  ------ Instantiation Options
% 3.07/1.02  
% 3.07/1.02  --instantiation_flag                    true
% 3.07/1.02  --inst_sos_flag                         false
% 3.07/1.02  --inst_sos_phase                        true
% 3.07/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.02  --inst_lit_sel_side                     num_symb
% 3.07/1.02  --inst_solver_per_active                1400
% 3.07/1.02  --inst_solver_calls_frac                1.
% 3.07/1.02  --inst_passive_queue_type               priority_queues
% 3.07/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.02  --inst_passive_queues_freq              [25;2]
% 3.07/1.02  --inst_dismatching                      true
% 3.07/1.02  --inst_eager_unprocessed_to_passive     true
% 3.07/1.02  --inst_prop_sim_given                   true
% 3.07/1.02  --inst_prop_sim_new                     false
% 3.07/1.02  --inst_subs_new                         false
% 3.07/1.02  --inst_eq_res_simp                      false
% 3.07/1.02  --inst_subs_given                       false
% 3.07/1.02  --inst_orphan_elimination               true
% 3.07/1.02  --inst_learning_loop_flag               true
% 3.07/1.02  --inst_learning_start                   3000
% 3.07/1.02  --inst_learning_factor                  2
% 3.07/1.02  --inst_start_prop_sim_after_learn       3
% 3.07/1.02  --inst_sel_renew                        solver
% 3.07/1.02  --inst_lit_activity_flag                true
% 3.07/1.02  --inst_restr_to_given                   false
% 3.07/1.02  --inst_activity_threshold               500
% 3.07/1.02  --inst_out_proof                        true
% 3.07/1.02  
% 3.07/1.02  ------ Resolution Options
% 3.07/1.02  
% 3.07/1.02  --resolution_flag                       true
% 3.07/1.02  --res_lit_sel                           adaptive
% 3.07/1.02  --res_lit_sel_side                      none
% 3.07/1.02  --res_ordering                          kbo
% 3.07/1.02  --res_to_prop_solver                    active
% 3.07/1.02  --res_prop_simpl_new                    false
% 3.07/1.02  --res_prop_simpl_given                  true
% 3.07/1.02  --res_passive_queue_type                priority_queues
% 3.07/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.02  --res_passive_queues_freq               [15;5]
% 3.07/1.02  --res_forward_subs                      full
% 3.07/1.02  --res_backward_subs                     full
% 3.07/1.02  --res_forward_subs_resolution           true
% 3.07/1.02  --res_backward_subs_resolution          true
% 3.07/1.02  --res_orphan_elimination                true
% 3.07/1.02  --res_time_limit                        2.
% 3.07/1.02  --res_out_proof                         true
% 3.07/1.02  
% 3.07/1.02  ------ Superposition Options
% 3.07/1.02  
% 3.07/1.02  --superposition_flag                    true
% 3.07/1.02  --sup_passive_queue_type                priority_queues
% 3.07/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.02  --demod_completeness_check              fast
% 3.07/1.02  --demod_use_ground                      true
% 3.07/1.02  --sup_to_prop_solver                    passive
% 3.07/1.02  --sup_prop_simpl_new                    true
% 3.07/1.02  --sup_prop_simpl_given                  true
% 3.07/1.02  --sup_fun_splitting                     false
% 3.07/1.02  --sup_smt_interval                      50000
% 3.07/1.02  
% 3.07/1.02  ------ Superposition Simplification Setup
% 3.07/1.02  
% 3.07/1.02  --sup_indices_passive                   []
% 3.07/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.02  --sup_full_bw                           [BwDemod]
% 3.07/1.02  --sup_immed_triv                        [TrivRules]
% 3.07/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.02  --sup_immed_bw_main                     []
% 3.07/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.02  
% 3.07/1.02  ------ Combination Options
% 3.07/1.02  
% 3.07/1.02  --comb_res_mult                         3
% 3.07/1.02  --comb_sup_mult                         2
% 3.07/1.02  --comb_inst_mult                        10
% 3.07/1.02  
% 3.07/1.02  ------ Debug Options
% 3.07/1.02  
% 3.07/1.02  --dbg_backtrace                         false
% 3.07/1.02  --dbg_dump_prop_clauses                 false
% 3.07/1.02  --dbg_dump_prop_clauses_file            -
% 3.07/1.02  --dbg_out_stat                          false
% 3.07/1.02  ------ Parsing...
% 3.07/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/1.02  
% 3.07/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.07/1.02  
% 3.07/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/1.02  
% 3.07/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/1.02  ------ Proving...
% 3.07/1.02  ------ Problem Properties 
% 3.07/1.02  
% 3.07/1.02  
% 3.07/1.02  clauses                                 34
% 3.07/1.02  conjectures                             8
% 3.07/1.02  EPR                                     16
% 3.07/1.02  Horn                                    21
% 3.07/1.02  unary                                   7
% 3.07/1.02  binary                                  11
% 3.07/1.02  lits                                    100
% 3.07/1.02  lits eq                                 3
% 3.07/1.02  fd_pure                                 0
% 3.07/1.02  fd_pseudo                               0
% 3.07/1.02  fd_cond                                 0
% 3.07/1.02  fd_pseudo_cond                          1
% 3.07/1.02  AC symbols                              0
% 3.07/1.02  
% 3.07/1.02  ------ Schedule dynamic 5 is on 
% 3.07/1.02  
% 3.07/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/1.02  
% 3.07/1.02  
% 3.07/1.02  ------ 
% 3.07/1.02  Current options:
% 3.07/1.02  ------ 
% 3.07/1.02  
% 3.07/1.02  ------ Input Options
% 3.07/1.02  
% 3.07/1.02  --out_options                           all
% 3.07/1.02  --tptp_safe_out                         true
% 3.07/1.02  --problem_path                          ""
% 3.07/1.02  --include_path                          ""
% 3.07/1.02  --clausifier                            res/vclausify_rel
% 3.07/1.02  --clausifier_options                    --mode clausify
% 3.07/1.02  --stdin                                 false
% 3.07/1.02  --stats_out                             all
% 3.07/1.02  
% 3.07/1.02  ------ General Options
% 3.07/1.02  
% 3.07/1.02  --fof                                   false
% 3.07/1.02  --time_out_real                         305.
% 3.07/1.02  --time_out_virtual                      -1.
% 3.07/1.02  --symbol_type_check                     false
% 3.07/1.02  --clausify_out                          false
% 3.07/1.02  --sig_cnt_out                           false
% 3.07/1.02  --trig_cnt_out                          false
% 3.07/1.02  --trig_cnt_out_tolerance                1.
% 3.07/1.02  --trig_cnt_out_sk_spl                   false
% 3.07/1.02  --abstr_cl_out                          false
% 3.07/1.02  
% 3.07/1.02  ------ Global Options
% 3.07/1.02  
% 3.07/1.02  --schedule                              default
% 3.07/1.02  --add_important_lit                     false
% 3.07/1.02  --prop_solver_per_cl                    1000
% 3.07/1.02  --min_unsat_core                        false
% 3.07/1.02  --soft_assumptions                      false
% 3.07/1.02  --soft_lemma_size                       3
% 3.07/1.02  --prop_impl_unit_size                   0
% 3.07/1.02  --prop_impl_unit                        []
% 3.07/1.02  --share_sel_clauses                     true
% 3.07/1.02  --reset_solvers                         false
% 3.07/1.02  --bc_imp_inh                            [conj_cone]
% 3.07/1.02  --conj_cone_tolerance                   3.
% 3.07/1.02  --extra_neg_conj                        none
% 3.07/1.02  --large_theory_mode                     true
% 3.07/1.02  --prolific_symb_bound                   200
% 3.07/1.02  --lt_threshold                          2000
% 3.07/1.02  --clause_weak_htbl                      true
% 3.07/1.02  --gc_record_bc_elim                     false
% 3.07/1.02  
% 3.07/1.02  ------ Preprocessing Options
% 3.07/1.02  
% 3.07/1.02  --preprocessing_flag                    true
% 3.07/1.02  --time_out_prep_mult                    0.1
% 3.07/1.02  --splitting_mode                        input
% 3.07/1.02  --splitting_grd                         true
% 3.07/1.02  --splitting_cvd                         false
% 3.07/1.02  --splitting_cvd_svl                     false
% 3.07/1.02  --splitting_nvd                         32
% 3.07/1.02  --sub_typing                            true
% 3.07/1.02  --prep_gs_sim                           true
% 3.07/1.02  --prep_unflatten                        true
% 3.07/1.02  --prep_res_sim                          true
% 3.07/1.02  --prep_upred                            true
% 3.07/1.02  --prep_sem_filter                       exhaustive
% 3.07/1.02  --prep_sem_filter_out                   false
% 3.07/1.02  --pred_elim                             true
% 3.07/1.02  --res_sim_input                         true
% 3.07/1.02  --eq_ax_congr_red                       true
% 3.07/1.02  --pure_diseq_elim                       true
% 3.07/1.02  --brand_transform                       false
% 3.07/1.02  --non_eq_to_eq                          false
% 3.07/1.02  --prep_def_merge                        true
% 3.07/1.02  --prep_def_merge_prop_impl              false
% 3.07/1.02  --prep_def_merge_mbd                    true
% 3.07/1.02  --prep_def_merge_tr_red                 false
% 3.07/1.02  --prep_def_merge_tr_cl                  false
% 3.07/1.02  --smt_preprocessing                     true
% 3.07/1.02  --smt_ac_axioms                         fast
% 3.07/1.02  --preprocessed_out                      false
% 3.07/1.02  --preprocessed_stats                    false
% 3.07/1.02  
% 3.07/1.02  ------ Abstraction refinement Options
% 3.07/1.02  
% 3.07/1.02  --abstr_ref                             []
% 3.07/1.02  --abstr_ref_prep                        false
% 3.07/1.02  --abstr_ref_until_sat                   false
% 3.07/1.02  --abstr_ref_sig_restrict                funpre
% 3.07/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.02  --abstr_ref_under                       []
% 3.07/1.02  
% 3.07/1.02  ------ SAT Options
% 3.07/1.02  
% 3.07/1.02  --sat_mode                              false
% 3.07/1.02  --sat_fm_restart_options                ""
% 3.07/1.02  --sat_gr_def                            false
% 3.07/1.02  --sat_epr_types                         true
% 3.07/1.02  --sat_non_cyclic_types                  false
% 3.07/1.02  --sat_finite_models                     false
% 3.07/1.02  --sat_fm_lemmas                         false
% 3.07/1.02  --sat_fm_prep                           false
% 3.07/1.02  --sat_fm_uc_incr                        true
% 3.07/1.02  --sat_out_model                         small
% 3.07/1.02  --sat_out_clauses                       false
% 3.07/1.02  
% 3.07/1.02  ------ QBF Options
% 3.07/1.02  
% 3.07/1.02  --qbf_mode                              false
% 3.07/1.02  --qbf_elim_univ                         false
% 3.07/1.02  --qbf_dom_inst                          none
% 3.07/1.02  --qbf_dom_pre_inst                      false
% 3.07/1.02  --qbf_sk_in                             false
% 3.07/1.02  --qbf_pred_elim                         true
% 3.07/1.02  --qbf_split                             512
% 3.07/1.02  
% 3.07/1.02  ------ BMC1 Options
% 3.07/1.02  
% 3.07/1.02  --bmc1_incremental                      false
% 3.07/1.02  --bmc1_axioms                           reachable_all
% 3.07/1.02  --bmc1_min_bound                        0
% 3.07/1.02  --bmc1_max_bound                        -1
% 3.07/1.02  --bmc1_max_bound_default                -1
% 3.07/1.02  --bmc1_symbol_reachability              true
% 3.07/1.02  --bmc1_property_lemmas                  false
% 3.07/1.02  --bmc1_k_induction                      false
% 3.07/1.02  --bmc1_non_equiv_states                 false
% 3.07/1.02  --bmc1_deadlock                         false
% 3.07/1.02  --bmc1_ucm                              false
% 3.07/1.02  --bmc1_add_unsat_core                   none
% 3.07/1.02  --bmc1_unsat_core_children              false
% 3.07/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.02  --bmc1_out_stat                         full
% 3.07/1.02  --bmc1_ground_init                      false
% 3.07/1.02  --bmc1_pre_inst_next_state              false
% 3.07/1.02  --bmc1_pre_inst_state                   false
% 3.07/1.02  --bmc1_pre_inst_reach_state             false
% 3.07/1.02  --bmc1_out_unsat_core                   false
% 3.07/1.02  --bmc1_aig_witness_out                  false
% 3.07/1.02  --bmc1_verbose                          false
% 3.07/1.02  --bmc1_dump_clauses_tptp                false
% 3.07/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.02  --bmc1_dump_file                        -
% 3.07/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.02  --bmc1_ucm_extend_mode                  1
% 3.07/1.02  --bmc1_ucm_init_mode                    2
% 3.07/1.02  --bmc1_ucm_cone_mode                    none
% 3.07/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.02  --bmc1_ucm_relax_model                  4
% 3.07/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.02  --bmc1_ucm_layered_model                none
% 3.07/1.02  --bmc1_ucm_max_lemma_size               10
% 3.07/1.02  
% 3.07/1.02  ------ AIG Options
% 3.07/1.02  
% 3.07/1.02  --aig_mode                              false
% 3.07/1.02  
% 3.07/1.02  ------ Instantiation Options
% 3.07/1.02  
% 3.07/1.02  --instantiation_flag                    true
% 3.07/1.02  --inst_sos_flag                         false
% 3.07/1.02  --inst_sos_phase                        true
% 3.07/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.02  --inst_lit_sel_side                     none
% 3.07/1.02  --inst_solver_per_active                1400
% 3.07/1.02  --inst_solver_calls_frac                1.
% 3.07/1.02  --inst_passive_queue_type               priority_queues
% 3.07/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.02  --inst_passive_queues_freq              [25;2]
% 3.07/1.02  --inst_dismatching                      true
% 3.07/1.02  --inst_eager_unprocessed_to_passive     true
% 3.07/1.02  --inst_prop_sim_given                   true
% 3.07/1.02  --inst_prop_sim_new                     false
% 3.07/1.02  --inst_subs_new                         false
% 3.07/1.02  --inst_eq_res_simp                      false
% 3.07/1.02  --inst_subs_given                       false
% 3.07/1.02  --inst_orphan_elimination               true
% 3.07/1.02  --inst_learning_loop_flag               true
% 3.07/1.02  --inst_learning_start                   3000
% 3.07/1.02  --inst_learning_factor                  2
% 3.07/1.02  --inst_start_prop_sim_after_learn       3
% 3.07/1.02  --inst_sel_renew                        solver
% 3.07/1.02  --inst_lit_activity_flag                true
% 3.07/1.02  --inst_restr_to_given                   false
% 3.07/1.02  --inst_activity_threshold               500
% 3.07/1.02  --inst_out_proof                        true
% 3.07/1.02  
% 3.07/1.02  ------ Resolution Options
% 3.07/1.02  
% 3.07/1.02  --resolution_flag                       false
% 3.07/1.02  --res_lit_sel                           adaptive
% 3.07/1.02  --res_lit_sel_side                      none
% 3.07/1.02  --res_ordering                          kbo
% 3.07/1.02  --res_to_prop_solver                    active
% 3.07/1.02  --res_prop_simpl_new                    false
% 3.07/1.02  --res_prop_simpl_given                  true
% 3.07/1.02  --res_passive_queue_type                priority_queues
% 3.07/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.02  --res_passive_queues_freq               [15;5]
% 3.07/1.02  --res_forward_subs                      full
% 3.07/1.02  --res_backward_subs                     full
% 3.07/1.02  --res_forward_subs_resolution           true
% 3.07/1.02  --res_backward_subs_resolution          true
% 3.07/1.02  --res_orphan_elimination                true
% 3.07/1.02  --res_time_limit                        2.
% 3.07/1.02  --res_out_proof                         true
% 3.07/1.02  
% 3.07/1.02  ------ Superposition Options
% 3.07/1.02  
% 3.07/1.02  --superposition_flag                    true
% 3.07/1.02  --sup_passive_queue_type                priority_queues
% 3.07/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.02  --demod_completeness_check              fast
% 3.07/1.02  --demod_use_ground                      true
% 3.07/1.02  --sup_to_prop_solver                    passive
% 3.07/1.02  --sup_prop_simpl_new                    true
% 3.07/1.02  --sup_prop_simpl_given                  true
% 3.07/1.02  --sup_fun_splitting                     false
% 3.07/1.02  --sup_smt_interval                      50000
% 3.07/1.02  
% 3.07/1.02  ------ Superposition Simplification Setup
% 3.07/1.02  
% 3.07/1.02  --sup_indices_passive                   []
% 3.07/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.02  --sup_full_bw                           [BwDemod]
% 3.07/1.02  --sup_immed_triv                        [TrivRules]
% 3.07/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.02  --sup_immed_bw_main                     []
% 3.07/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.02  
% 3.07/1.02  ------ Combination Options
% 3.07/1.02  
% 3.07/1.02  --comb_res_mult                         3
% 3.07/1.02  --comb_sup_mult                         2
% 3.07/1.02  --comb_inst_mult                        10
% 3.07/1.02  
% 3.07/1.02  ------ Debug Options
% 3.07/1.02  
% 3.07/1.02  --dbg_backtrace                         false
% 3.07/1.02  --dbg_dump_prop_clauses                 false
% 3.07/1.02  --dbg_dump_prop_clauses_file            -
% 3.07/1.02  --dbg_out_stat                          false
% 3.07/1.02  
% 3.07/1.02  
% 3.07/1.02  
% 3.07/1.02  
% 3.07/1.02  ------ Proving...
% 3.07/1.02  
% 3.07/1.02  
% 3.07/1.02  % SZS status Theorem for theBenchmark.p
% 3.07/1.02  
% 3.07/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/1.02  
% 3.07/1.02  fof(f1,axiom,(
% 3.07/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f54,plain,(
% 3.07/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.02    inference(nnf_transformation,[],[f1])).
% 3.07/1.02  
% 3.07/1.02  fof(f55,plain,(
% 3.07/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.02    inference(rectify,[],[f54])).
% 3.07/1.02  
% 3.07/1.02  fof(f56,plain,(
% 3.07/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.07/1.02    introduced(choice_axiom,[])).
% 3.07/1.02  
% 3.07/1.02  fof(f57,plain,(
% 3.07/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).
% 3.07/1.02  
% 3.07/1.02  fof(f73,plain,(
% 3.07/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f57])).
% 3.07/1.02  
% 3.07/1.02  fof(f21,conjecture,(
% 3.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f22,negated_conjecture,(
% 3.07/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.07/1.02    inference(negated_conjecture,[],[f21])).
% 3.07/1.02  
% 3.07/1.02  fof(f52,plain,(
% 3.07/1.02    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.07/1.02    inference(ennf_transformation,[],[f22])).
% 3.07/1.02  
% 3.07/1.02  fof(f53,plain,(
% 3.07/1.02    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.07/1.02    inference(flattening,[],[f52])).
% 3.07/1.02  
% 3.07/1.02  fof(f67,plain,(
% 3.07/1.02    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.07/1.02    inference(nnf_transformation,[],[f53])).
% 3.07/1.02  
% 3.07/1.02  fof(f68,plain,(
% 3.07/1.02    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.07/1.02    inference(flattening,[],[f67])).
% 3.07/1.02  
% 3.07/1.02  fof(f70,plain,(
% 3.07/1.02    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK5) | ~v2_tex_2(sK5,X0)) & (v1_zfmisc_1(sK5) | v2_tex_2(sK5,X0)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK5))) )),
% 3.07/1.02    introduced(choice_axiom,[])).
% 3.07/1.02  
% 3.07/1.02  fof(f69,plain,(
% 3.07/1.02    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK4)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.07/1.02    introduced(choice_axiom,[])).
% 3.07/1.02  
% 3.07/1.02  fof(f71,plain,(
% 3.07/1.02    ((~v1_zfmisc_1(sK5) | ~v2_tex_2(sK5,sK4)) & (v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f68,f70,f69])).
% 3.07/1.02  
% 3.07/1.02  fof(f107,plain,(
% 3.07/1.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  fof(f9,axiom,(
% 3.07/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f30,plain,(
% 3.07/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.07/1.02    inference(ennf_transformation,[],[f9])).
% 3.07/1.02  
% 3.07/1.02  fof(f31,plain,(
% 3.07/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.07/1.02    inference(flattening,[],[f30])).
% 3.07/1.02  
% 3.07/1.02  fof(f85,plain,(
% 3.07/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f31])).
% 3.07/1.02  
% 3.07/1.02  fof(f13,axiom,(
% 3.07/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f36,plain,(
% 3.07/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.07/1.02    inference(ennf_transformation,[],[f13])).
% 3.07/1.02  
% 3.07/1.02  fof(f37,plain,(
% 3.07/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.07/1.02    inference(flattening,[],[f36])).
% 3.07/1.02  
% 3.07/1.02  fof(f89,plain,(
% 3.07/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f37])).
% 3.07/1.02  
% 3.07/1.02  fof(f106,plain,(
% 3.07/1.02    ~v1_xboole_0(sK5)),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  fof(f8,axiom,(
% 3.07/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f64,plain,(
% 3.07/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.07/1.02    inference(nnf_transformation,[],[f8])).
% 3.07/1.02  
% 3.07/1.02  fof(f83,plain,(
% 3.07/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.07/1.02    inference(cnf_transformation,[],[f64])).
% 3.07/1.02  
% 3.07/1.02  fof(f7,axiom,(
% 3.07/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f29,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.07/1.02    inference(ennf_transformation,[],[f7])).
% 3.07/1.02  
% 3.07/1.02  fof(f82,plain,(
% 3.07/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f29])).
% 3.07/1.02  
% 3.07/1.02  fof(f84,plain,(
% 3.07/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f64])).
% 3.07/1.02  
% 3.07/1.02  fof(f20,axiom,(
% 3.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f50,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.07/1.02    inference(ennf_transformation,[],[f20])).
% 3.07/1.02  
% 3.07/1.02  fof(f51,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/1.02    inference(flattening,[],[f50])).
% 3.07/1.02  
% 3.07/1.02  fof(f101,plain,(
% 3.07/1.02    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f51])).
% 3.07/1.02  
% 3.07/1.02  fof(f102,plain,(
% 3.07/1.02    ~v2_struct_0(sK4)),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  fof(f103,plain,(
% 3.07/1.02    v2_pre_topc(sK4)),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  fof(f105,plain,(
% 3.07/1.02    l1_pre_topc(sK4)),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  fof(f108,plain,(
% 3.07/1.02    v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4)),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  fof(f19,axiom,(
% 3.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f23,plain,(
% 3.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.07/1.02    inference(pure_predicate_removal,[],[f19])).
% 3.07/1.02  
% 3.07/1.02  fof(f48,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.07/1.02    inference(ennf_transformation,[],[f23])).
% 3.07/1.02  
% 3.07/1.02  fof(f49,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/1.02    inference(flattening,[],[f48])).
% 3.07/1.02  
% 3.07/1.02  fof(f65,plain,(
% 3.07/1.02    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))))),
% 3.07/1.02    introduced(choice_axiom,[])).
% 3.07/1.02  
% 3.07/1.02  fof(f66,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f65])).
% 3.07/1.02  
% 3.07/1.02  fof(f100,plain,(
% 3.07/1.02    ( ! [X0,X1] : (u1_struct_0(sK3(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f66])).
% 3.07/1.02  
% 3.07/1.02  fof(f6,axiom,(
% 3.07/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f28,plain,(
% 3.07/1.02    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.07/1.02    inference(ennf_transformation,[],[f6])).
% 3.07/1.02  
% 3.07/1.02  fof(f81,plain,(
% 3.07/1.02    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f28])).
% 3.07/1.02  
% 3.07/1.02  fof(f18,axiom,(
% 3.07/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f46,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.07/1.02    inference(ennf_transformation,[],[f18])).
% 3.07/1.02  
% 3.07/1.02  fof(f47,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.07/1.02    inference(flattening,[],[f46])).
% 3.07/1.02  
% 3.07/1.02  fof(f96,plain,(
% 3.07/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f47])).
% 3.07/1.02  
% 3.07/1.02  fof(f4,axiom,(
% 3.07/1.02    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f78,plain,(
% 3.07/1.02    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.07/1.02    inference(cnf_transformation,[],[f4])).
% 3.07/1.02  
% 3.07/1.02  fof(f16,axiom,(
% 3.07/1.02    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f42,plain,(
% 3.07/1.02    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.07/1.02    inference(ennf_transformation,[],[f16])).
% 3.07/1.02  
% 3.07/1.02  fof(f43,plain,(
% 3.07/1.02    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.07/1.02    inference(flattening,[],[f42])).
% 3.07/1.02  
% 3.07/1.02  fof(f93,plain,(
% 3.07/1.02    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f43])).
% 3.07/1.02  
% 3.07/1.02  fof(f15,axiom,(
% 3.07/1.02    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f40,plain,(
% 3.07/1.02    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.07/1.02    inference(ennf_transformation,[],[f15])).
% 3.07/1.02  
% 3.07/1.02  fof(f41,plain,(
% 3.07/1.02    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.07/1.02    inference(flattening,[],[f40])).
% 3.07/1.02  
% 3.07/1.02  fof(f91,plain,(
% 3.07/1.02    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f41])).
% 3.07/1.02  
% 3.07/1.02  fof(f10,axiom,(
% 3.07/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f32,plain,(
% 3.07/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.07/1.02    inference(ennf_transformation,[],[f10])).
% 3.07/1.02  
% 3.07/1.02  fof(f86,plain,(
% 3.07/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f32])).
% 3.07/1.02  
% 3.07/1.02  fof(f12,axiom,(
% 3.07/1.02    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f34,plain,(
% 3.07/1.02    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.07/1.02    inference(ennf_transformation,[],[f12])).
% 3.07/1.02  
% 3.07/1.02  fof(f35,plain,(
% 3.07/1.02    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.07/1.02    inference(flattening,[],[f34])).
% 3.07/1.02  
% 3.07/1.02  fof(f88,plain,(
% 3.07/1.02    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f35])).
% 3.07/1.02  
% 3.07/1.02  fof(f97,plain,(
% 3.07/1.02    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f66])).
% 3.07/1.02  
% 3.07/1.02  fof(f98,plain,(
% 3.07/1.02    ( ! [X0,X1] : (v1_tdlat_3(sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f66])).
% 3.07/1.02  
% 3.07/1.02  fof(f99,plain,(
% 3.07/1.02    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f66])).
% 3.07/1.02  
% 3.07/1.02  fof(f11,axiom,(
% 3.07/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f33,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.07/1.02    inference(ennf_transformation,[],[f11])).
% 3.07/1.02  
% 3.07/1.02  fof(f87,plain,(
% 3.07/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f33])).
% 3.07/1.02  
% 3.07/1.02  fof(f17,axiom,(
% 3.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.02  
% 3.07/1.02  fof(f44,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.07/1.02    inference(ennf_transformation,[],[f17])).
% 3.07/1.02  
% 3.07/1.02  fof(f45,plain,(
% 3.07/1.02    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/1.02    inference(flattening,[],[f44])).
% 3.07/1.02  
% 3.07/1.02  fof(f95,plain,(
% 3.07/1.02    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/1.02    inference(cnf_transformation,[],[f45])).
% 3.07/1.02  
% 3.07/1.02  fof(f104,plain,(
% 3.07/1.02    v2_tdlat_3(sK4)),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  fof(f109,plain,(
% 3.07/1.02    ~v1_zfmisc_1(sK5) | ~v2_tex_2(sK5,sK4)),
% 3.07/1.02    inference(cnf_transformation,[],[f71])).
% 3.07/1.02  
% 3.07/1.02  cnf(c_0,plain,
% 3.07/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4033,plain,
% 3.07/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.07/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_32,negated_conjecture,
% 3.07/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.07/1.02      inference(cnf_transformation,[],[f107]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4009,plain,
% 3.07/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_13,plain,
% 3.07/1.02      ( m1_subset_1(X0,X1)
% 3.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.07/1.02      | ~ r2_hidden(X0,X2) ),
% 3.07/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4021,plain,
% 3.07/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 3.07/1.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.07/1.02      | r2_hidden(X0,X2) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5510,plain,
% 3.07/1.02      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 3.07/1.02      | r2_hidden(X0,sK5) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4009,c_4021]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_17,plain,
% 3.07/1.02      ( ~ m1_subset_1(X0,X1)
% 3.07/1.02      | v1_xboole_0(X1)
% 3.07/1.02      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4019,plain,
% 3.07/1.02      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.07/1.02      | m1_subset_1(X1,X0) != iProver_top
% 3.07/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5566,plain,
% 3.07/1.02      ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
% 3.07/1.02      | r2_hidden(X0,sK5) != iProver_top
% 3.07/1.02      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_5510,c_4019]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_33,negated_conjecture,
% 3.07/1.02      ( ~ v1_xboole_0(sK5) ),
% 3.07/1.02      inference(cnf_transformation,[],[f106]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_42,plain,
% 3.07/1.02      ( v1_xboole_0(sK5) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_12,plain,
% 3.07/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.07/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4022,plain,
% 3.07/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.07/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4712,plain,
% 3.07/1.02      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4009,c_4022]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_10,plain,
% 3.07/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.07/1.02      | ~ v1_xboole_0(X1)
% 3.07/1.02      | v1_xboole_0(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_11,plain,
% 3.07/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.07/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_290,plain,
% 3.07/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.07/1.02      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_291,plain,
% 3.07/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_290]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_358,plain,
% 3.07/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.07/1.02      inference(bin_hyper_res,[status(thm)],[c_10,c_291]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4002,plain,
% 3.07/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.07/1.02      | v1_xboole_0(X1) != iProver_top
% 3.07/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5057,plain,
% 3.07/1.02      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4712,c_4002]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5675,plain,
% 3.07/1.02      ( r2_hidden(X0,sK5) != iProver_top
% 3.07/1.02      | k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0) ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_5566,c_42,c_5057]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5676,plain,
% 3.07/1.02      ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
% 3.07/1.02      | r2_hidden(X0,sK5) != iProver_top ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_5675]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5683,plain,
% 3.07/1.02      ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4033,c_5676]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_43,plain,
% 3.07/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4330,plain,
% 3.07/1.02      ( r2_hidden(sK0(sK5),sK5) | v1_xboole_0(sK5) ),
% 3.07/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4331,plain,
% 3.07/1.02      ( r2_hidden(sK0(sK5),sK5) = iProver_top
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_4330]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4519,plain,
% 3.07/1.02      ( m1_subset_1(sK0(sK5),X0)
% 3.07/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.07/1.02      | ~ r2_hidden(sK0(sK5),sK5) ),
% 3.07/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4702,plain,
% 3.07/1.02      ( m1_subset_1(sK0(sK5),u1_struct_0(sK4))
% 3.07/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/1.02      | ~ r2_hidden(sK0(sK5),sK5) ),
% 3.07/1.02      inference(instantiation,[status(thm)],[c_4519]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4703,plain,
% 3.07/1.02      ( m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top
% 3.07/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.07/1.02      | r2_hidden(sK0(sK5),sK5) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_4702]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4846,plain,
% 3.07/1.02      ( ~ m1_subset_1(sK0(sK5),u1_struct_0(sK4))
% 3.07/1.02      | v1_xboole_0(u1_struct_0(sK4))
% 3.07/1.02      | k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5)) ),
% 3.07/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4852,plain,
% 3.07/1.02      ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
% 3.07/1.02      | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.07/1.02      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_4846]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5704,plain,
% 3.07/1.02      ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5)) ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_5683,c_42,c_43,c_4331,c_4703,c_4852,c_5057]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_29,plain,
% 3.07/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.07/1.02      | v2_struct_0(X0)
% 3.07/1.02      | ~ v2_pre_topc(X0)
% 3.07/1.02      | ~ l1_pre_topc(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f101]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4012,plain,
% 3.07/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.07/1.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.07/1.02      | v2_struct_0(X0) = iProver_top
% 3.07/1.02      | v2_pre_topc(X0) != iProver_top
% 3.07/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5707,plain,
% 3.07/1.02      ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top
% 3.07/1.02      | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.07/1.02      | v2_struct_0(sK4) = iProver_top
% 3.07/1.02      | v2_pre_topc(sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_5704,c_4012]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_37,negated_conjecture,
% 3.07/1.02      ( ~ v2_struct_0(sK4) ),
% 3.07/1.02      inference(cnf_transformation,[],[f102]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_38,plain,
% 3.07/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_36,negated_conjecture,
% 3.07/1.02      ( v2_pre_topc(sK4) ),
% 3.07/1.02      inference(cnf_transformation,[],[f103]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_39,plain,
% 3.07/1.02      ( v2_pre_topc(sK4) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_34,negated_conjecture,
% 3.07/1.02      ( l1_pre_topc(sK4) ),
% 3.07/1.02      inference(cnf_transformation,[],[f105]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_41,plain,
% 3.07/1.02      ( l1_pre_topc(sK4) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_9407,plain,
% 3.07/1.02      ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_5707,c_38,c_39,c_41,c_42,c_43,c_4331,c_4703]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_31,negated_conjecture,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) ),
% 3.07/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4010,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.07/1.02      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_25,plain,
% 3.07/1.02      ( ~ v2_tex_2(X0,X1)
% 3.07/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | ~ v2_pre_topc(X1)
% 3.07/1.02      | ~ l1_pre_topc(X1)
% 3.07/1.02      | v1_xboole_0(X0)
% 3.07/1.02      | u1_struct_0(sK3(X1,X0)) = X0 ),
% 3.07/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4016,plain,
% 3.07/1.02      ( u1_struct_0(sK3(X0,X1)) = X1
% 3.07/1.02      | v2_tex_2(X1,X0) != iProver_top
% 3.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.07/1.02      | v2_struct_0(X0) = iProver_top
% 3.07/1.02      | v2_pre_topc(X0) != iProver_top
% 3.07/1.02      | l1_pre_topc(X0) != iProver_top
% 3.07/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5975,plain,
% 3.07/1.02      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.07/1.02      | v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v2_struct_0(sK4) = iProver_top
% 3.07/1.02      | v2_pre_topc(sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4009,c_4016]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6354,plain,
% 3.07/1.02      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.07/1.02      | v2_tex_2(sK5,sK4) != iProver_top ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_5975,c_38,c_39,c_41,c_42]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6360,plain,
% 3.07/1.02      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.07/1.02      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4010,c_6354]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_9,plain,
% 3.07/1.02      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 3.07/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4024,plain,
% 3.07/1.02      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
% 3.07/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4763,plain,
% 3.07/1.02      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 3.07/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4024,c_4022]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_24,plain,
% 3.07/1.02      ( ~ r1_tarski(X0,X1)
% 3.07/1.02      | ~ v1_zfmisc_1(X1)
% 3.07/1.02      | v1_xboole_0(X0)
% 3.07/1.02      | v1_xboole_0(X1)
% 3.07/1.02      | X1 = X0 ),
% 3.07/1.02      inference(cnf_transformation,[],[f96]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_208,plain,
% 3.07/1.02      ( v1_xboole_0(X0)
% 3.07/1.02      | ~ v1_zfmisc_1(X1)
% 3.07/1.02      | ~ r1_tarski(X0,X1)
% 3.07/1.02      | X1 = X0 ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_24,c_11,c_10]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_209,plain,
% 3.07/1.02      ( ~ r1_tarski(X0,X1)
% 3.07/1.02      | ~ v1_zfmisc_1(X1)
% 3.07/1.02      | v1_xboole_0(X0)
% 3.07/1.02      | X1 = X0 ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_208]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4003,plain,
% 3.07/1.02      ( X0 = X1
% 3.07/1.02      | r1_tarski(X1,X0) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(X0) != iProver_top
% 3.07/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5271,plain,
% 3.07/1.02      ( k1_tarski(X0) = X1
% 3.07/1.02      | r2_hidden(X0,X1) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(X1) != iProver_top
% 3.07/1.02      | v1_xboole_0(k1_tarski(X0)) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4763,c_4003]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6,plain,
% 3.07/1.02      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.07/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_101,plain,
% 3.07/1.02      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6681,plain,
% 3.07/1.02      ( v1_zfmisc_1(X1) != iProver_top
% 3.07/1.02      | r2_hidden(X0,X1) != iProver_top
% 3.07/1.02      | k1_tarski(X0) = X1 ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_5271,c_101]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6682,plain,
% 3.07/1.02      ( k1_tarski(X0) = X1
% 3.07/1.02      | r2_hidden(X0,X1) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(X1) != iProver_top ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_6681]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6690,plain,
% 3.07/1.02      ( k1_tarski(sK0(X0)) = X0
% 3.07/1.02      | v1_zfmisc_1(X0) != iProver_top
% 3.07/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4033,c_6682]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6812,plain,
% 3.07/1.02      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.07/1.02      | k1_tarski(sK0(sK5)) = sK5
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_6360,c_6690]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6834,plain,
% 3.07/1.02      ( v1_xboole_0(sK5)
% 3.07/1.02      | u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.07/1.02      | k1_tarski(sK0(sK5)) = sK5 ),
% 3.07/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_6812]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7035,plain,
% 3.07/1.02      ( k1_tarski(sK0(sK5)) = sK5 | u1_struct_0(sK3(sK4,sK5)) = sK5 ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_6812,c_33,c_6834]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7036,plain,
% 3.07/1.02      ( u1_struct_0(sK3(sK4,sK5)) = sK5 | k1_tarski(sK0(sK5)) = sK5 ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_7035]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7040,plain,
% 3.07/1.02      ( k1_tarski(sK0(sK5)) = sK5
% 3.07/1.02      | v2_tex_2(k6_domain_1(sK5,X0),sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | m1_subset_1(X0,u1_struct_0(sK3(sK4,sK5))) != iProver_top
% 3.07/1.02      | v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | v2_pre_topc(sK3(sK4,sK5)) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_7036,c_4012]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_21,plain,
% 3.07/1.02      ( v2_struct_0(X0)
% 3.07/1.02      | ~ v2_tdlat_3(X0)
% 3.07/1.02      | ~ v1_tdlat_3(X0)
% 3.07/1.02      | ~ v2_pre_topc(X0)
% 3.07/1.02      | v7_struct_0(X0)
% 3.07/1.02      | ~ l1_pre_topc(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_19,plain,
% 3.07/1.02      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_214,plain,
% 3.07/1.02      ( ~ v1_tdlat_3(X0)
% 3.07/1.02      | ~ v2_tdlat_3(X0)
% 3.07/1.02      | v2_struct_0(X0)
% 3.07/1.02      | v7_struct_0(X0)
% 3.07/1.02      | ~ l1_pre_topc(X0) ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_21,c_19]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_215,plain,
% 3.07/1.02      ( v2_struct_0(X0)
% 3.07/1.02      | ~ v2_tdlat_3(X0)
% 3.07/1.02      | ~ v1_tdlat_3(X0)
% 3.07/1.02      | v7_struct_0(X0)
% 3.07/1.02      | ~ l1_pre_topc(X0) ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_214]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_14,plain,
% 3.07/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_16,plain,
% 3.07/1.02      ( ~ v7_struct_0(X0)
% 3.07/1.02      | v1_zfmisc_1(u1_struct_0(X0))
% 3.07/1.02      | ~ l1_struct_0(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_488,plain,
% 3.07/1.02      ( ~ v7_struct_0(X0)
% 3.07/1.02      | v1_zfmisc_1(u1_struct_0(X0))
% 3.07/1.02      | ~ l1_pre_topc(X0) ),
% 3.07/1.02      inference(resolution,[status(thm)],[c_14,c_16]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_506,plain,
% 3.07/1.02      ( v2_struct_0(X0)
% 3.07/1.02      | ~ v2_tdlat_3(X0)
% 3.07/1.02      | ~ v1_tdlat_3(X0)
% 3.07/1.02      | v1_zfmisc_1(u1_struct_0(X0))
% 3.07/1.02      | ~ l1_pre_topc(X0) ),
% 3.07/1.02      inference(resolution,[status(thm)],[c_215,c_488]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4001,plain,
% 3.07/1.02      ( v2_struct_0(X0) = iProver_top
% 3.07/1.02      | v2_tdlat_3(X0) != iProver_top
% 3.07/1.02      | v1_tdlat_3(X0) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 3.07/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7041,plain,
% 3.07/1.02      ( k1_tarski(sK0(sK5)) = sK5
% 3.07/1.02      | v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.07/1.02      | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(sK5) = iProver_top
% 3.07/1.02      | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_7036,c_4001]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_44,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.07/1.02      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_28,plain,
% 3.07/1.02      ( ~ v2_tex_2(X0,X1)
% 3.07/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | ~ v2_struct_0(sK3(X1,X0))
% 3.07/1.02      | ~ v2_pre_topc(X1)
% 3.07/1.02      | ~ l1_pre_topc(X1)
% 3.07/1.02      | v1_xboole_0(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f97]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_294,plain,
% 3.07/1.02      ( v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) ),
% 3.07/1.02      inference(prop_impl,[status(thm)],[c_31]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_295,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_294]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_886,plain,
% 3.07/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | ~ v2_struct_0(sK3(X1,X0))
% 3.07/1.02      | ~ v2_pre_topc(X1)
% 3.07/1.02      | v1_zfmisc_1(sK5)
% 3.07/1.02      | ~ l1_pre_topc(X1)
% 3.07/1.02      | v1_xboole_0(X0)
% 3.07/1.02      | sK4 != X1
% 3.07/1.02      | sK5 != X0 ),
% 3.07/1.02      inference(resolution_lifted,[status(thm)],[c_28,c_295]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_887,plain,
% 3.07/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/1.02      | ~ v2_struct_0(sK3(sK4,sK5))
% 3.07/1.02      | v2_struct_0(sK4)
% 3.07/1.02      | ~ v2_pre_topc(sK4)
% 3.07/1.02      | v1_zfmisc_1(sK5)
% 3.07/1.02      | ~ l1_pre_topc(sK4)
% 3.07/1.02      | v1_xboole_0(sK5) ),
% 3.07/1.02      inference(unflattening,[status(thm)],[c_886]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_889,plain,
% 3.07/1.02      ( ~ v2_struct_0(sK3(sK4,sK5)) | v1_zfmisc_1(sK5) ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_887,c_37,c_36,c_34,c_33,c_32]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_891,plain,
% 3.07/1.02      ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_27,plain,
% 3.07/1.02      ( ~ v2_tex_2(X0,X1)
% 3.07/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | v1_tdlat_3(sK3(X1,X0))
% 3.07/1.02      | ~ v2_pre_topc(X1)
% 3.07/1.02      | ~ l1_pre_topc(X1)
% 3.07/1.02      | v1_xboole_0(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_900,plain,
% 3.07/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | v1_tdlat_3(sK3(X1,X0))
% 3.07/1.02      | ~ v2_pre_topc(X1)
% 3.07/1.02      | v1_zfmisc_1(sK5)
% 3.07/1.02      | ~ l1_pre_topc(X1)
% 3.07/1.02      | v1_xboole_0(X0)
% 3.07/1.02      | sK4 != X1
% 3.07/1.02      | sK5 != X0 ),
% 3.07/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_295]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_901,plain,
% 3.07/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/1.02      | v2_struct_0(sK4)
% 3.07/1.02      | v1_tdlat_3(sK3(sK4,sK5))
% 3.07/1.02      | ~ v2_pre_topc(sK4)
% 3.07/1.02      | v1_zfmisc_1(sK5)
% 3.07/1.02      | ~ l1_pre_topc(sK4)
% 3.07/1.02      | v1_xboole_0(sK5) ),
% 3.07/1.02      inference(unflattening,[status(thm)],[c_900]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_903,plain,
% 3.07/1.02      ( v1_tdlat_3(sK3(sK4,sK5)) | v1_zfmisc_1(sK5) ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_901,c_37,c_36,c_34,c_33,c_32]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_905,plain,
% 3.07/1.02      ( v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_26,plain,
% 3.07/1.02      ( ~ v2_tex_2(X0,X1)
% 3.07/1.02      | m1_pre_topc(sK3(X1,X0),X1)
% 3.07/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | ~ v2_pre_topc(X1)
% 3.07/1.02      | ~ l1_pre_topc(X1)
% 3.07/1.02      | v1_xboole_0(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f99]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4015,plain,
% 3.07/1.02      ( v2_tex_2(X0,X1) != iProver_top
% 3.07/1.02      | m1_pre_topc(sK3(X1,X0),X1) = iProver_top
% 3.07/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.07/1.02      | v2_struct_0(X1) = iProver_top
% 3.07/1.02      | v2_pre_topc(X1) != iProver_top
% 3.07/1.02      | l1_pre_topc(X1) != iProver_top
% 3.07/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6051,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
% 3.07/1.02      | v2_struct_0(sK4) = iProver_top
% 3.07/1.02      | v2_pre_topc(sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4009,c_4015]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6494,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_6051,c_38,c_39,c_41,c_42]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_15,plain,
% 3.07/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.07/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4020,plain,
% 3.07/1.02      ( m1_pre_topc(X0,X1) != iProver_top
% 3.07/1.02      | l1_pre_topc(X1) != iProver_top
% 3.07/1.02      | l1_pre_topc(X0) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6500,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_6494,c_4020]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_23,plain,
% 3.07/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | ~ v2_tdlat_3(X1)
% 3.07/1.02      | v2_tdlat_3(X0)
% 3.07/1.02      | ~ v2_pre_topc(X1)
% 3.07/1.02      | ~ l1_pre_topc(X1) ),
% 3.07/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_1150,plain,
% 3.07/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | ~ v2_tdlat_3(X2)
% 3.07/1.02      | ~ v2_tdlat_3(X1)
% 3.07/1.02      | v2_tdlat_3(X0)
% 3.07/1.02      | ~ l1_pre_topc(X2)
% 3.07/1.02      | ~ l1_pre_topc(X1)
% 3.07/1.02      | X1 != X2 ),
% 3.07/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_1151,plain,
% 3.07/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.07/1.02      | v2_struct_0(X1)
% 3.07/1.02      | ~ v2_tdlat_3(X1)
% 3.07/1.02      | v2_tdlat_3(X0)
% 3.07/1.02      | ~ l1_pre_topc(X1) ),
% 3.07/1.02      inference(unflattening,[status(thm)],[c_1150]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4000,plain,
% 3.07/1.02      ( m1_pre_topc(X0,X1) != iProver_top
% 3.07/1.02      | v2_struct_0(X1) = iProver_top
% 3.07/1.02      | v2_tdlat_3(X1) != iProver_top
% 3.07/1.02      | v2_tdlat_3(X0) = iProver_top
% 3.07/1.02      | l1_pre_topc(X1) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6501,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v2_struct_0(sK4) = iProver_top
% 3.07/1.02      | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | v2_tdlat_3(sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_6494,c_4000]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_35,negated_conjecture,
% 3.07/1.02      ( v2_tdlat_3(sK4) ),
% 3.07/1.02      inference(cnf_transformation,[],[f104]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_40,plain,
% 3.07/1.02      ( v2_tdlat_3(sK4) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6585,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_6501,c_38,c_40,c_41]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7241,plain,
% 3.07/1.02      ( v1_zfmisc_1(sK5) = iProver_top | k1_tarski(sK0(sK5)) = sK5 ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_7041,c_38,c_40,c_41,c_44,c_891,c_905,c_6500,c_6501]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7242,plain,
% 3.07/1.02      ( k1_tarski(sK0(sK5)) = sK5 | v1_zfmisc_1(sK5) = iProver_top ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_7241]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7247,plain,
% 3.07/1.02      ( k1_tarski(sK0(sK5)) = sK5 | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_7242,c_6690]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7308,plain,
% 3.07/1.02      ( k1_tarski(sK0(sK5)) = sK5 ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_7040,c_42,c_7247]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_9411,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) = iProver_top ),
% 3.07/1.02      inference(light_normalisation,[status(thm)],[c_9407,c_7308]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_9414,plain,
% 3.07/1.02      ( u1_struct_0(sK3(sK4,sK5)) = sK5 ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_9411,c_6354]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_9544,plain,
% 3.07/1.02      ( v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.07/1.02      | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(sK5) = iProver_top
% 3.07/1.02      | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_9414,c_4001]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7311,plain,
% 3.07/1.02      ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = sK5 ),
% 3.07/1.02      inference(demodulation,[status(thm)],[c_7308,c_5704]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_7641,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.07/1.02      | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.07/1.02      | v2_struct_0(sK4) = iProver_top
% 3.07/1.02      | v2_pre_topc(sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_7311,c_4012]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4013,plain,
% 3.07/1.02      ( v2_tex_2(X0,X1) != iProver_top
% 3.07/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.07/1.02      | v2_struct_0(X1) = iProver_top
% 3.07/1.02      | v2_struct_0(sK3(X1,X0)) != iProver_top
% 3.07/1.02      | v2_pre_topc(X1) != iProver_top
% 3.07/1.02      | l1_pre_topc(X1) != iProver_top
% 3.07/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5793,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v2_struct_0(sK3(sK4,sK5)) != iProver_top
% 3.07/1.02      | v2_struct_0(sK4) = iProver_top
% 3.07/1.02      | v2_pre_topc(sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4009,c_4013]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6487,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v2_struct_0(sK3(sK4,sK5)) != iProver_top ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_5793,c_38,c_39,c_41,c_42]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_4014,plain,
% 3.07/1.02      ( v2_tex_2(X0,X1) != iProver_top
% 3.07/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.07/1.02      | v2_struct_0(X1) = iProver_top
% 3.07/1.02      | v1_tdlat_3(sK3(X1,X0)) = iProver_top
% 3.07/1.02      | v2_pre_topc(X1) != iProver_top
% 3.07/1.02      | l1_pre_topc(X1) != iProver_top
% 3.07/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_5869,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v2_struct_0(sK4) = iProver_top
% 3.07/1.02      | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | v2_pre_topc(sK4) != iProver_top
% 3.07/1.02      | l1_pre_topc(sK4) != iProver_top
% 3.07/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.07/1.02      inference(superposition,[status(thm)],[c_4009,c_4014]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6266,plain,
% 3.07/1.02      ( v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.07/1.02      | v2_tex_2(sK5,sK4) != iProver_top ),
% 3.07/1.02      inference(global_propositional_subsumption,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_5869,c_38,c_39,c_41,c_42]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_6267,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
% 3.07/1.02      inference(renaming,[status(thm)],[c_6266]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_30,negated_conjecture,
% 3.07/1.02      ( ~ v2_tex_2(sK5,sK4) | ~ v1_zfmisc_1(sK5) ),
% 3.07/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(c_45,plain,
% 3.07/1.02      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.07/1.02      | v1_zfmisc_1(sK5) != iProver_top ),
% 3.07/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.07/1.02  
% 3.07/1.02  cnf(contradiction,plain,
% 3.07/1.02      ( $false ),
% 3.07/1.02      inference(minisat,
% 3.07/1.02                [status(thm)],
% 3.07/1.02                [c_9544,c_7641,c_6585,c_6500,c_6487,c_6267,c_4703,c_4331,
% 3.07/1.02                 c_45,c_43,c_42,c_41,c_39,c_38]) ).
% 3.07/1.02  
% 3.07/1.02  
% 3.07/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/1.02  
% 3.07/1.02  ------                               Statistics
% 3.07/1.02  
% 3.07/1.02  ------ General
% 3.07/1.02  
% 3.07/1.02  abstr_ref_over_cycles:                  0
% 3.07/1.02  abstr_ref_under_cycles:                 0
% 3.07/1.02  gc_basic_clause_elim:                   0
% 3.07/1.02  forced_gc_time:                         0
% 3.07/1.02  parsing_time:                           0.022
% 3.07/1.02  unif_index_cands_time:                  0.
% 3.07/1.02  unif_index_add_time:                    0.
% 3.07/1.02  orderings_time:                         0.
% 3.07/1.02  out_proof_time:                         0.014
% 3.07/1.02  total_time:                             0.251
% 3.07/1.02  num_of_symbols:                         55
% 3.07/1.02  num_of_terms:                           5403
% 3.07/1.02  
% 3.07/1.02  ------ Preprocessing
% 3.07/1.02  
% 3.07/1.02  num_of_splits:                          0
% 3.07/1.02  num_of_split_atoms:                     0
% 3.07/1.02  num_of_reused_defs:                     0
% 3.07/1.02  num_eq_ax_congr_red:                    38
% 3.07/1.02  num_of_sem_filtered_clauses:            1
% 3.07/1.02  num_of_subtypes:                        0
% 3.07/1.02  monotx_restored_types:                  0
% 3.07/1.02  sat_num_of_epr_types:                   0
% 3.07/1.02  sat_num_of_non_cyclic_types:            0
% 3.07/1.02  sat_guarded_non_collapsed_types:        0
% 3.07/1.02  num_pure_diseq_elim:                    0
% 3.07/1.02  simp_replaced_by:                       0
% 3.07/1.02  res_preprocessed:                       171
% 3.07/1.02  prep_upred:                             0
% 3.07/1.02  prep_unflattend:                        96
% 3.07/1.02  smt_new_axioms:                         0
% 3.07/1.02  pred_elim_cands:                        12
% 3.07/1.02  pred_elim:                              2
% 3.07/1.02  pred_elim_cl:                           2
% 3.07/1.02  pred_elim_cycles:                       14
% 3.07/1.02  merged_defs:                            16
% 3.07/1.02  merged_defs_ncl:                        0
% 3.07/1.02  bin_hyper_res:                          17
% 3.07/1.02  prep_cycles:                            4
% 3.07/1.02  pred_elim_time:                         0.039
% 3.07/1.02  splitting_time:                         0.
% 3.07/1.02  sem_filter_time:                        0.
% 3.07/1.02  monotx_time:                            0.001
% 3.07/1.02  subtype_inf_time:                       0.
% 3.07/1.02  
% 3.07/1.02  ------ Problem properties
% 3.07/1.02  
% 3.07/1.02  clauses:                                34
% 3.07/1.02  conjectures:                            8
% 3.07/1.02  epr:                                    16
% 3.07/1.02  horn:                                   21
% 3.07/1.02  ground:                                 8
% 3.07/1.02  unary:                                  7
% 3.07/1.02  binary:                                 11
% 3.07/1.02  lits:                                   100
% 3.07/1.02  lits_eq:                                3
% 3.07/1.02  fd_pure:                                0
% 3.07/1.02  fd_pseudo:                              0
% 3.07/1.02  fd_cond:                                0
% 3.07/1.02  fd_pseudo_cond:                         1
% 3.07/1.02  ac_symbols:                             0
% 3.07/1.02  
% 3.07/1.02  ------ Propositional Solver
% 3.07/1.02  
% 3.07/1.02  prop_solver_calls:                      28
% 3.07/1.02  prop_fast_solver_calls:                 2026
% 3.07/1.02  smt_solver_calls:                       0
% 3.07/1.02  smt_fast_solver_calls:                  0
% 3.07/1.02  prop_num_of_clauses:                    2566
% 3.07/1.02  prop_preprocess_simplified:             8428
% 3.07/1.02  prop_fo_subsumed:                       149
% 3.07/1.02  prop_solver_time:                       0.
% 3.07/1.02  smt_solver_time:                        0.
% 3.07/1.02  smt_fast_solver_time:                   0.
% 3.07/1.02  prop_fast_solver_time:                  0.
% 3.07/1.02  prop_unsat_core_time:                   0.
% 3.07/1.02  
% 3.07/1.02  ------ QBF
% 3.07/1.02  
% 3.07/1.02  qbf_q_res:                              0
% 3.07/1.02  qbf_num_tautologies:                    0
% 3.07/1.02  qbf_prep_cycles:                        0
% 3.07/1.02  
% 3.07/1.02  ------ BMC1
% 3.07/1.02  
% 3.07/1.02  bmc1_current_bound:                     -1
% 3.07/1.02  bmc1_last_solved_bound:                 -1
% 3.07/1.02  bmc1_unsat_core_size:                   -1
% 3.07/1.02  bmc1_unsat_core_parents_size:           -1
% 3.07/1.02  bmc1_merge_next_fun:                    0
% 3.07/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.07/1.02  
% 3.07/1.02  ------ Instantiation
% 3.07/1.02  
% 3.07/1.02  inst_num_of_clauses:                    615
% 3.07/1.02  inst_num_in_passive:                    55
% 3.07/1.02  inst_num_in_active:                     368
% 3.07/1.02  inst_num_in_unprocessed:                193
% 3.07/1.02  inst_num_of_loops:                      510
% 3.07/1.02  inst_num_of_learning_restarts:          0
% 3.07/1.02  inst_num_moves_active_passive:          139
% 3.07/1.02  inst_lit_activity:                      0
% 3.07/1.02  inst_lit_activity_moves:                0
% 3.07/1.02  inst_num_tautologies:                   0
% 3.07/1.02  inst_num_prop_implied:                  0
% 3.07/1.02  inst_num_existing_simplified:           0
% 3.07/1.02  inst_num_eq_res_simplified:             0
% 3.07/1.02  inst_num_child_elim:                    0
% 3.07/1.02  inst_num_of_dismatching_blockings:      206
% 3.07/1.02  inst_num_of_non_proper_insts:           694
% 3.07/1.02  inst_num_of_duplicates:                 0
% 3.07/1.02  inst_inst_num_from_inst_to_res:         0
% 3.07/1.02  inst_dismatching_checking_time:         0.
% 3.07/1.03  
% 3.07/1.03  ------ Resolution
% 3.07/1.03  
% 3.07/1.03  res_num_of_clauses:                     0
% 3.07/1.03  res_num_in_passive:                     0
% 3.07/1.03  res_num_in_active:                      0
% 3.07/1.03  res_num_of_loops:                       175
% 3.07/1.03  res_forward_subset_subsumed:            49
% 3.07/1.03  res_backward_subset_subsumed:           4
% 3.07/1.03  res_forward_subsumed:                   1
% 3.07/1.03  res_backward_subsumed:                  1
% 3.07/1.03  res_forward_subsumption_resolution:     1
% 3.07/1.03  res_backward_subsumption_resolution:    0
% 3.07/1.03  res_clause_to_clause_subsumption:       420
% 3.07/1.03  res_orphan_elimination:                 0
% 3.07/1.03  res_tautology_del:                      109
% 3.07/1.03  res_num_eq_res_simplified:              0
% 3.07/1.03  res_num_sel_changes:                    0
% 3.07/1.03  res_moves_from_active_to_pass:          0
% 3.07/1.03  
% 3.07/1.03  ------ Superposition
% 3.07/1.03  
% 3.07/1.03  sup_time_total:                         0.
% 3.07/1.03  sup_time_generating:                    0.
% 3.07/1.03  sup_time_sim_full:                      0.
% 3.07/1.03  sup_time_sim_immed:                     0.
% 3.07/1.03  
% 3.07/1.03  sup_num_of_clauses:                     166
% 3.07/1.03  sup_num_in_active:                      95
% 3.07/1.03  sup_num_in_passive:                     71
% 3.07/1.03  sup_num_of_loops:                       100
% 3.07/1.03  sup_fw_superposition:                   103
% 3.07/1.03  sup_bw_superposition:                   81
% 3.07/1.03  sup_immediate_simplified:               20
% 3.07/1.03  sup_given_eliminated:                   0
% 3.07/1.03  comparisons_done:                       0
% 3.07/1.03  comparisons_avoided:                    8
% 3.07/1.03  
% 3.07/1.03  ------ Simplifications
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  sim_fw_subset_subsumed:                 10
% 3.07/1.03  sim_bw_subset_subsumed:                 11
% 3.07/1.03  sim_fw_subsumed:                        7
% 3.07/1.03  sim_bw_subsumed:                        0
% 3.07/1.03  sim_fw_subsumption_res:                 0
% 3.07/1.03  sim_bw_subsumption_res:                 0
% 3.07/1.03  sim_tautology_del:                      7
% 3.07/1.03  sim_eq_tautology_del:                   3
% 3.07/1.03  sim_eq_res_simp:                        0
% 3.07/1.03  sim_fw_demodulated:                     0
% 3.07/1.03  sim_bw_demodulated:                     1
% 3.07/1.03  sim_light_normalised:                   6
% 3.07/1.03  sim_joinable_taut:                      0
% 3.07/1.03  sim_joinable_simp:                      0
% 3.07/1.03  sim_ac_normalised:                      0
% 3.07/1.03  sim_smt_subsumption:                    0
% 3.07/1.03  
%------------------------------------------------------------------------------
