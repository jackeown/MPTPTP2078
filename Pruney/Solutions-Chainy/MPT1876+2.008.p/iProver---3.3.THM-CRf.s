%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:48 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  288 (3620 expanded)
%              Number of clauses        :  173 (1075 expanded)
%              Number of leaves         :   27 ( 771 expanded)
%              Depth                    :   26
%              Number of atoms          : 1141 (18259 expanded)
%              Number of equality atoms :  294 (1645 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
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

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f68])).

fof(f114,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK4)
          | ~ v2_tex_2(sK4,X0) )
        & ( v1_zfmisc_1(sK4)
          | v2_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
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
            | ~ v2_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v2_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v2_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f71,f73,f72])).

fof(f121,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f115,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f116,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f118,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f119,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

fof(f120,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f74])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f61,f62])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f91,f80])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f82,f80])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f80])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f107,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f123,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f81,f80])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f127,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f122,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f88,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f90,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f89,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f117,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_40,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_382,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_40])).

cnf(c_383,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_1837,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_383])).

cnf(c_1838,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_1837])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1840,plain,
    ( v1_zfmisc_1(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1838,c_46,c_45,c_43,c_42,c_41])).

cnf(c_6354,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1840])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6395,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6390,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6958,plain,
    ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_6390])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_6385,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9087,plain,
    ( k2_tarski(sK1(X0,X1),sK1(X0,X1)) = k6_domain_1(X0,sK1(X0,X1))
    | r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6958,c_6385])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6397,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6957,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_6397])).

cnf(c_21535,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | k2_tarski(sK1(X0,X1),sK1(X0,X1)) = k6_domain_1(X0,sK1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9087,c_6957])).

cnf(c_21536,plain,
    ( k2_tarski(sK1(X0,X1),sK1(X0,X1)) = k6_domain_1(X0,sK1(X0,X1))
    | r1_tarski(X0,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_21535])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6398,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6741,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6398,c_6390])).

cnf(c_8648,plain,
    ( k2_tarski(sK0(X0),sK0(X0)) = k6_domain_1(X0,sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6741,c_6385])).

cnf(c_6372,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_9181,plain,
    ( k2_tarski(sK0(sK4),sK0(sK4)) = k6_domain_1(sK4,sK0(sK4)) ),
    inference(superposition,[status(thm)],[c_8648,c_6372])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_tarski(X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_6391,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9197,plain,
    ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),X0) != iProver_top
    | r2_hidden(sK0(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9181,c_6391])).

cnf(c_21544,plain,
    ( k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),X0),sK1(k6_domain_1(sK4,sK0(sK4)),X0)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),X0))
    | r2_hidden(sK0(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_21536,c_9197])).

cnf(c_6,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_6392,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6374,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7880,plain,
    ( k2_tarski(X0,X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6392,c_6374])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_138,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_148,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17673,plain,
    ( k2_tarski(X0,X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7880,c_138,c_148])).

cnf(c_21578,plain,
    ( k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),X0),sK1(k6_domain_1(sK4,sK0(sK4)),X0)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),X0))
    | k2_tarski(sK0(sK4),sK0(sK4)) = X0
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21544,c_17673])).

cnf(c_21598,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = X0
    | k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),X0),sK1(k6_domain_1(sK4,sK0(sK4)),X0)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),X0))
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21578,c_9181])).

cnf(c_21657,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = sK4
    | k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),sK4),sK1(k6_domain_1(sK4,sK0(sK4)),sK4)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),sK4))
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_6354,c_21598])).

cnf(c_6373,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6388,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6791,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6373,c_6388])).

cnf(c_6792,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6791])).

cnf(c_7961,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6588,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8720,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(sK0(sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_6588])).

cnf(c_6521,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9851,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6521])).

cnf(c_25,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6461,plain,
    ( m1_pre_topc(k1_tex_2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_10466,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3)
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6461])).

cnf(c_9196,plain,
    ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),X0) = iProver_top
    | r2_hidden(sK0(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9181,c_6392])).

cnf(c_6394,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9280,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k6_domain_1(sK4,sK0(sK4))) != iProver_top
    | r2_hidden(sK0(sK4),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9196,c_6394])).

cnf(c_9647,plain,
    ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),X0) = iProver_top
    | r2_hidden(sK1(k6_domain_1(sK4,sK0(sK4)),X0),X1) = iProver_top
    | r2_hidden(sK0(sK4),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_9280])).

cnf(c_7299,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6791,c_6394])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6396,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7320,plain,
    ( r1_tarski(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7299,c_6396])).

cnf(c_11317,plain,
    ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9647,c_7320])).

cnf(c_51,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_7962,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7961])).

cnf(c_11501,plain,
    ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11317,c_51,c_7962])).

cnf(c_11507,plain,
    ( r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11501,c_9197])).

cnf(c_12068,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11507,c_6390])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_6376,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k1_tex_2(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12072,plain,
    ( v2_struct_0(k1_tex_2(sK3,sK0(sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12068,c_6376])).

cnf(c_12077,plain,
    ( ~ v2_struct_0(k1_tex_2(sK3,sK0(sK4)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12072])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6375,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v7_struct_0(k1_tex_2(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12074,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v7_struct_0(k1_tex_2(sK3,sK0(sK4))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12068,c_6375])).

cnf(c_12079,plain,
    ( v2_struct_0(sK3)
    | v7_struct_0(k1_tex_2(sK3,sK0(sK4)))
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12074])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_25])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_289,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_30,c_28])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_6367,plain,
    ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_13261,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = u1_struct_0(k1_tex_2(sK3,sK0(sK4)))
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12068,c_6367])).

cnf(c_7319,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7299,c_6390])).

cnf(c_7524,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0)
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7319,c_6385])).

cnf(c_7318,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7299,c_6397])).

cnf(c_7669,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7524,c_7318])).

cnf(c_7670,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7669])).

cnf(c_7675,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k2_tarski(sK0(sK4),sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6398,c_7670])).

cnf(c_7807,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k2_tarski(sK0(sK4),sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7675,c_51])).

cnf(c_9190,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k6_domain_1(sK4,sK0(sK4)) ),
    inference(demodulation,[status(thm)],[c_9181,c_7807])).

cnf(c_13264,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK0(sK4))) = k6_domain_1(sK4,sK0(sK4))
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13261,c_9190])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_50,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_13544,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK0(sK4))) = k6_domain_1(sK4,sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13264,c_47,c_50])).

cnf(c_32,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_269,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_16])).

cnf(c_270,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_39,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_380,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_39])).

cnf(c_381,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_1727,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK4
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_270,c_381])).

cnf(c_1728,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != sK4 ),
    inference(unflattening,[status(thm)],[c_1727])).

cnf(c_1732,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_46,c_43])).

cnf(c_1733,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v1_zfmisc_1(sK4)
    | u1_struct_0(X0) != sK4 ),
    inference(renaming,[status(thm)],[c_1732])).

cnf(c_6360,plain,
    ( u1_struct_0(X0) != sK4
    | m1_pre_topc(X0,sK3) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1733])).

cnf(c_13553,plain,
    ( k6_domain_1(sK4,sK0(sK4)) != sK4
    | m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3) != iProver_top
    | v1_tdlat_3(k1_tex_2(sK3,sK0(sK4))) != iProver_top
    | v2_struct_0(k1_tex_2(sK3,sK0(sK4))) = iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_13544,c_6360])).

cnf(c_8721,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8720])).

cnf(c_9281,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = X0
    | r2_hidden(sK0(sK4),X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k6_domain_1(sK4,sK0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9196,c_6374])).

cnf(c_6393,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9198,plain,
    ( v1_xboole_0(k6_domain_1(sK4,sK0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9181,c_6393])).

cnf(c_9820,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | r2_hidden(sK0(sK4),X0) != iProver_top
    | k6_domain_1(sK4,sK0(sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9281,c_9198])).

cnf(c_9821,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = X0
    | r2_hidden(sK0(sK4),X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9820])).

cnf(c_9826,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6398,c_9821])).

cnf(c_9852,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9851])).

cnf(c_10467,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10466])).

cnf(c_16283,plain,
    ( v1_tdlat_3(k1_tex_2(sK3,sK0(sK4))) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13553,c_47,c_50,c_51,c_6791,c_7962,c_8721,c_9826,c_9852,c_10467,c_12072])).

cnf(c_16285,plain,
    ( ~ v1_tdlat_3(k1_tex_2(sK3,sK0(sK4)))
    | ~ v1_zfmisc_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16283])).

cnf(c_6378,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6387,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7922,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(k1_tex_2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6378,c_6387])).

cnf(c_19273,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(k1_tex_2(sK3,sK0(sK4))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12068,c_7922])).

cnf(c_19289,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_pre_topc(k1_tex_2(sK3,sK0(sK4)))
    | ~ v2_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19273])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6479,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6815,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),sK3)
    | v1_tdlat_3(k1_tex_2(X0,X1))
    | v2_struct_0(k1_tex_2(X0,X1))
    | v2_struct_0(sK3)
    | ~ v7_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k1_tex_2(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6479])).

cnf(c_21021,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3)
    | v1_tdlat_3(k1_tex_2(sK3,sK0(sK4)))
    | v2_struct_0(k1_tex_2(sK3,sK0(sK4)))
    | v2_struct_0(sK3)
    | ~ v7_struct_0(k1_tex_2(sK3,sK0(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k1_tex_2(sK3,sK0(sK4))) ),
    inference(instantiation,[status(thm)],[c_6815])).

cnf(c_21959,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21657,c_46,c_45,c_43,c_42,c_41,c_1838,c_6792,c_7961,c_8720,c_9851,c_10466,c_12077,c_12079,c_16285,c_19289,c_21021])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_14,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_611,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_12,c_14])).

cnf(c_6366,plain,
    ( v7_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_21975,plain,
    ( v7_struct_0(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21959,c_6366])).

cnf(c_21022,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3) != iProver_top
    | v1_tdlat_3(k1_tex_2(sK3,sK0(sK4))) = iProver_top
    | v2_struct_0(k1_tex_2(sK3,sK0(sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v7_struct_0(k1_tex_2(sK3,sK0(sK4))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(k1_tex_2(sK3,sK0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21021])).

cnf(c_35,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1823,plain,
    ( m1_pre_topc(sK2(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v1_xboole_0(X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_383])).

cnf(c_1824,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1823])).

cnf(c_1826,plain,
    ( v1_zfmisc_1(sK4)
    | m1_pre_topc(sK2(sK3,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1824,c_46,c_45,c_43,c_42,c_41])).

cnf(c_1827,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_1826])).

cnf(c_6355,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1827])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_6380,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v7_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8501,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_tdlat_3(sK3) != iProver_top
    | v7_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6355,c_6380])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6386,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7035,plain,
    ( v1_zfmisc_1(sK4) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6355,c_6386])).

cnf(c_36,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1809,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | v2_struct_0(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_383])).

cnf(c_1810,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,sK4))
    | v2_struct_0(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1809])).

cnf(c_1812,plain,
    ( v1_zfmisc_1(sK4)
    | v1_tdlat_3(sK2(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1810,c_46,c_45,c_43,c_42,c_41])).

cnf(c_1813,plain,
    ( v1_tdlat_3(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_1812])).

cnf(c_1814,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_38,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1781,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_383])).

cnf(c_1782,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,sK4))
    | v2_struct_0(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1781])).

cnf(c_1784,plain,
    ( v1_zfmisc_1(sK4)
    | ~ v2_struct_0(sK2(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1782,c_46,c_45,c_43,c_42,c_41])).

cnf(c_1785,plain,
    ( ~ v2_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_1784])).

cnf(c_1786,plain,
    ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_44,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_49,plain,
    ( v2_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_48,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21975,c_21022,c_19273,c_16283,c_12074,c_12072,c_10467,c_9852,c_8721,c_8501,c_7962,c_7035,c_6791,c_1814,c_1786,c_51,c_50,c_49,c_48,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:38:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.26/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/1.48  
% 7.26/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.48  
% 7.26/1.48  ------  iProver source info
% 7.26/1.48  
% 7.26/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.48  git: non_committed_changes: false
% 7.26/1.48  git: last_make_outside_of_git: false
% 7.26/1.48  
% 7.26/1.48  ------ 
% 7.26/1.48  
% 7.26/1.48  ------ Input Options
% 7.26/1.48  
% 7.26/1.48  --out_options                           all
% 7.26/1.48  --tptp_safe_out                         true
% 7.26/1.48  --problem_path                          ""
% 7.26/1.48  --include_path                          ""
% 7.26/1.48  --clausifier                            res/vclausify_rel
% 7.26/1.48  --clausifier_options                    ""
% 7.26/1.48  --stdin                                 false
% 7.26/1.48  --stats_out                             all
% 7.26/1.48  
% 7.26/1.48  ------ General Options
% 7.26/1.48  
% 7.26/1.48  --fof                                   false
% 7.26/1.48  --time_out_real                         305.
% 7.26/1.48  --time_out_virtual                      -1.
% 7.26/1.48  --symbol_type_check                     false
% 7.26/1.48  --clausify_out                          false
% 7.26/1.48  --sig_cnt_out                           false
% 7.26/1.48  --trig_cnt_out                          false
% 7.26/1.48  --trig_cnt_out_tolerance                1.
% 7.26/1.48  --trig_cnt_out_sk_spl                   false
% 7.26/1.48  --abstr_cl_out                          false
% 7.26/1.48  
% 7.26/1.48  ------ Global Options
% 7.26/1.48  
% 7.26/1.48  --schedule                              default
% 7.26/1.48  --add_important_lit                     false
% 7.26/1.48  --prop_solver_per_cl                    1000
% 7.26/1.48  --min_unsat_core                        false
% 7.26/1.48  --soft_assumptions                      false
% 7.26/1.48  --soft_lemma_size                       3
% 7.26/1.48  --prop_impl_unit_size                   0
% 7.26/1.48  --prop_impl_unit                        []
% 7.26/1.48  --share_sel_clauses                     true
% 7.26/1.48  --reset_solvers                         false
% 7.26/1.48  --bc_imp_inh                            [conj_cone]
% 7.26/1.48  --conj_cone_tolerance                   3.
% 7.26/1.48  --extra_neg_conj                        none
% 7.26/1.48  --large_theory_mode                     true
% 7.26/1.48  --prolific_symb_bound                   200
% 7.26/1.48  --lt_threshold                          2000
% 7.26/1.48  --clause_weak_htbl                      true
% 7.26/1.48  --gc_record_bc_elim                     false
% 7.26/1.48  
% 7.26/1.48  ------ Preprocessing Options
% 7.26/1.48  
% 7.26/1.48  --preprocessing_flag                    true
% 7.26/1.48  --time_out_prep_mult                    0.1
% 7.26/1.48  --splitting_mode                        input
% 7.26/1.48  --splitting_grd                         true
% 7.26/1.48  --splitting_cvd                         false
% 7.26/1.48  --splitting_cvd_svl                     false
% 7.26/1.48  --splitting_nvd                         32
% 7.26/1.48  --sub_typing                            true
% 7.26/1.48  --prep_gs_sim                           true
% 7.26/1.48  --prep_unflatten                        true
% 7.26/1.48  --prep_res_sim                          true
% 7.26/1.48  --prep_upred                            true
% 7.26/1.48  --prep_sem_filter                       exhaustive
% 7.26/1.48  --prep_sem_filter_out                   false
% 7.26/1.48  --pred_elim                             true
% 7.26/1.48  --res_sim_input                         true
% 7.26/1.48  --eq_ax_congr_red                       true
% 7.26/1.48  --pure_diseq_elim                       true
% 7.26/1.48  --brand_transform                       false
% 7.26/1.48  --non_eq_to_eq                          false
% 7.26/1.48  --prep_def_merge                        true
% 7.26/1.48  --prep_def_merge_prop_impl              false
% 7.26/1.48  --prep_def_merge_mbd                    true
% 7.26/1.48  --prep_def_merge_tr_red                 false
% 7.26/1.48  --prep_def_merge_tr_cl                  false
% 7.26/1.48  --smt_preprocessing                     true
% 7.26/1.48  --smt_ac_axioms                         fast
% 7.26/1.48  --preprocessed_out                      false
% 7.26/1.48  --preprocessed_stats                    false
% 7.26/1.48  
% 7.26/1.48  ------ Abstraction refinement Options
% 7.26/1.48  
% 7.26/1.48  --abstr_ref                             []
% 7.26/1.48  --abstr_ref_prep                        false
% 7.26/1.48  --abstr_ref_until_sat                   false
% 7.26/1.48  --abstr_ref_sig_restrict                funpre
% 7.26/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.48  --abstr_ref_under                       []
% 7.26/1.48  
% 7.26/1.48  ------ SAT Options
% 7.26/1.48  
% 7.26/1.48  --sat_mode                              false
% 7.26/1.48  --sat_fm_restart_options                ""
% 7.26/1.48  --sat_gr_def                            false
% 7.26/1.48  --sat_epr_types                         true
% 7.26/1.48  --sat_non_cyclic_types                  false
% 7.26/1.48  --sat_finite_models                     false
% 7.26/1.48  --sat_fm_lemmas                         false
% 7.26/1.48  --sat_fm_prep                           false
% 7.26/1.48  --sat_fm_uc_incr                        true
% 7.26/1.48  --sat_out_model                         small
% 7.26/1.48  --sat_out_clauses                       false
% 7.26/1.48  
% 7.26/1.48  ------ QBF Options
% 7.26/1.48  
% 7.26/1.48  --qbf_mode                              false
% 7.26/1.48  --qbf_elim_univ                         false
% 7.26/1.48  --qbf_dom_inst                          none
% 7.26/1.48  --qbf_dom_pre_inst                      false
% 7.26/1.48  --qbf_sk_in                             false
% 7.26/1.48  --qbf_pred_elim                         true
% 7.26/1.48  --qbf_split                             512
% 7.26/1.48  
% 7.26/1.48  ------ BMC1 Options
% 7.26/1.48  
% 7.26/1.48  --bmc1_incremental                      false
% 7.26/1.48  --bmc1_axioms                           reachable_all
% 7.26/1.48  --bmc1_min_bound                        0
% 7.26/1.48  --bmc1_max_bound                        -1
% 7.26/1.48  --bmc1_max_bound_default                -1
% 7.26/1.48  --bmc1_symbol_reachability              true
% 7.26/1.48  --bmc1_property_lemmas                  false
% 7.26/1.48  --bmc1_k_induction                      false
% 7.26/1.48  --bmc1_non_equiv_states                 false
% 7.26/1.48  --bmc1_deadlock                         false
% 7.26/1.48  --bmc1_ucm                              false
% 7.26/1.48  --bmc1_add_unsat_core                   none
% 7.26/1.48  --bmc1_unsat_core_children              false
% 7.26/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.48  --bmc1_out_stat                         full
% 7.26/1.48  --bmc1_ground_init                      false
% 7.26/1.48  --bmc1_pre_inst_next_state              false
% 7.26/1.48  --bmc1_pre_inst_state                   false
% 7.26/1.48  --bmc1_pre_inst_reach_state             false
% 7.26/1.48  --bmc1_out_unsat_core                   false
% 7.26/1.48  --bmc1_aig_witness_out                  false
% 7.26/1.48  --bmc1_verbose                          false
% 7.26/1.48  --bmc1_dump_clauses_tptp                false
% 7.26/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.48  --bmc1_dump_file                        -
% 7.26/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.48  --bmc1_ucm_extend_mode                  1
% 7.26/1.48  --bmc1_ucm_init_mode                    2
% 7.26/1.48  --bmc1_ucm_cone_mode                    none
% 7.26/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.48  --bmc1_ucm_relax_model                  4
% 7.26/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.48  --bmc1_ucm_layered_model                none
% 7.26/1.48  --bmc1_ucm_max_lemma_size               10
% 7.26/1.48  
% 7.26/1.48  ------ AIG Options
% 7.26/1.48  
% 7.26/1.48  --aig_mode                              false
% 7.26/1.48  
% 7.26/1.48  ------ Instantiation Options
% 7.26/1.48  
% 7.26/1.48  --instantiation_flag                    true
% 7.26/1.48  --inst_sos_flag                         true
% 7.26/1.48  --inst_sos_phase                        true
% 7.26/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.48  --inst_lit_sel_side                     num_symb
% 7.26/1.48  --inst_solver_per_active                1400
% 7.26/1.48  --inst_solver_calls_frac                1.
% 7.26/1.48  --inst_passive_queue_type               priority_queues
% 7.26/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.48  --inst_passive_queues_freq              [25;2]
% 7.26/1.48  --inst_dismatching                      true
% 7.26/1.48  --inst_eager_unprocessed_to_passive     true
% 7.26/1.48  --inst_prop_sim_given                   true
% 7.26/1.48  --inst_prop_sim_new                     false
% 7.26/1.48  --inst_subs_new                         false
% 7.26/1.48  --inst_eq_res_simp                      false
% 7.26/1.48  --inst_subs_given                       false
% 7.26/1.48  --inst_orphan_elimination               true
% 7.26/1.48  --inst_learning_loop_flag               true
% 7.26/1.48  --inst_learning_start                   3000
% 7.26/1.48  --inst_learning_factor                  2
% 7.26/1.48  --inst_start_prop_sim_after_learn       3
% 7.26/1.48  --inst_sel_renew                        solver
% 7.26/1.48  --inst_lit_activity_flag                true
% 7.26/1.48  --inst_restr_to_given                   false
% 7.26/1.48  --inst_activity_threshold               500
% 7.26/1.48  --inst_out_proof                        true
% 7.26/1.48  
% 7.26/1.48  ------ Resolution Options
% 7.26/1.48  
% 7.26/1.48  --resolution_flag                       true
% 7.26/1.48  --res_lit_sel                           adaptive
% 7.26/1.48  --res_lit_sel_side                      none
% 7.26/1.48  --res_ordering                          kbo
% 7.26/1.48  --res_to_prop_solver                    active
% 7.26/1.48  --res_prop_simpl_new                    false
% 7.26/1.48  --res_prop_simpl_given                  true
% 7.26/1.48  --res_passive_queue_type                priority_queues
% 7.26/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.48  --res_passive_queues_freq               [15;5]
% 7.26/1.48  --res_forward_subs                      full
% 7.26/1.48  --res_backward_subs                     full
% 7.26/1.48  --res_forward_subs_resolution           true
% 7.26/1.48  --res_backward_subs_resolution          true
% 7.26/1.48  --res_orphan_elimination                true
% 7.26/1.48  --res_time_limit                        2.
% 7.26/1.48  --res_out_proof                         true
% 7.26/1.48  
% 7.26/1.48  ------ Superposition Options
% 7.26/1.48  
% 7.26/1.48  --superposition_flag                    true
% 7.26/1.48  --sup_passive_queue_type                priority_queues
% 7.26/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.48  --demod_completeness_check              fast
% 7.26/1.48  --demod_use_ground                      true
% 7.26/1.48  --sup_to_prop_solver                    passive
% 7.26/1.48  --sup_prop_simpl_new                    true
% 7.26/1.48  --sup_prop_simpl_given                  true
% 7.26/1.48  --sup_fun_splitting                     true
% 7.26/1.48  --sup_smt_interval                      50000
% 7.26/1.48  
% 7.26/1.48  ------ Superposition Simplification Setup
% 7.26/1.48  
% 7.26/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.26/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.26/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.26/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.26/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.26/1.48  --sup_immed_triv                        [TrivRules]
% 7.26/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.48  --sup_immed_bw_main                     []
% 7.26/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.26/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.48  --sup_input_bw                          []
% 7.26/1.48  
% 7.26/1.48  ------ Combination Options
% 7.26/1.48  
% 7.26/1.48  --comb_res_mult                         3
% 7.26/1.48  --comb_sup_mult                         2
% 7.26/1.48  --comb_inst_mult                        10
% 7.26/1.48  
% 7.26/1.48  ------ Debug Options
% 7.26/1.48  
% 7.26/1.48  --dbg_backtrace                         false
% 7.26/1.48  --dbg_dump_prop_clauses                 false
% 7.26/1.48  --dbg_dump_prop_clauses_file            -
% 7.26/1.48  --dbg_out_stat                          false
% 7.26/1.48  ------ Parsing...
% 7.26/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.48  
% 7.26/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.26/1.48  
% 7.26/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.48  
% 7.26/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.48  ------ Proving...
% 7.26/1.48  ------ Problem Properties 
% 7.26/1.48  
% 7.26/1.48  
% 7.26/1.48  clauses                                 45
% 7.26/1.48  conjectures                             6
% 7.26/1.48  EPR                                     15
% 7.26/1.48  Horn                                    23
% 7.26/1.48  unary                                   7
% 7.26/1.48  binary                                  14
% 7.26/1.48  lits                                    162
% 7.26/1.48  lits eq                                 9
% 7.26/1.48  fd_pure                                 0
% 7.26/1.48  fd_pseudo                               0
% 7.26/1.48  fd_cond                                 0
% 7.26/1.48  fd_pseudo_cond                          2
% 7.26/1.48  AC symbols                              0
% 7.26/1.48  
% 7.26/1.48  ------ Schedule dynamic 5 is on 
% 7.26/1.48  
% 7.26/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.26/1.48  
% 7.26/1.48  
% 7.26/1.48  ------ 
% 7.26/1.48  Current options:
% 7.26/1.48  ------ 
% 7.26/1.48  
% 7.26/1.48  ------ Input Options
% 7.26/1.48  
% 7.26/1.48  --out_options                           all
% 7.26/1.48  --tptp_safe_out                         true
% 7.26/1.48  --problem_path                          ""
% 7.26/1.48  --include_path                          ""
% 7.26/1.48  --clausifier                            res/vclausify_rel
% 7.26/1.48  --clausifier_options                    ""
% 7.26/1.48  --stdin                                 false
% 7.26/1.48  --stats_out                             all
% 7.26/1.48  
% 7.26/1.48  ------ General Options
% 7.26/1.48  
% 7.26/1.48  --fof                                   false
% 7.26/1.48  --time_out_real                         305.
% 7.26/1.48  --time_out_virtual                      -1.
% 7.26/1.48  --symbol_type_check                     false
% 7.26/1.48  --clausify_out                          false
% 7.26/1.48  --sig_cnt_out                           false
% 7.26/1.48  --trig_cnt_out                          false
% 7.26/1.48  --trig_cnt_out_tolerance                1.
% 7.26/1.48  --trig_cnt_out_sk_spl                   false
% 7.26/1.48  --abstr_cl_out                          false
% 7.26/1.48  
% 7.26/1.48  ------ Global Options
% 7.26/1.48  
% 7.26/1.48  --schedule                              default
% 7.26/1.48  --add_important_lit                     false
% 7.26/1.48  --prop_solver_per_cl                    1000
% 7.26/1.48  --min_unsat_core                        false
% 7.26/1.48  --soft_assumptions                      false
% 7.26/1.48  --soft_lemma_size                       3
% 7.26/1.48  --prop_impl_unit_size                   0
% 7.26/1.48  --prop_impl_unit                        []
% 7.26/1.48  --share_sel_clauses                     true
% 7.26/1.48  --reset_solvers                         false
% 7.26/1.48  --bc_imp_inh                            [conj_cone]
% 7.26/1.48  --conj_cone_tolerance                   3.
% 7.26/1.48  --extra_neg_conj                        none
% 7.26/1.48  --large_theory_mode                     true
% 7.26/1.48  --prolific_symb_bound                   200
% 7.26/1.48  --lt_threshold                          2000
% 7.26/1.48  --clause_weak_htbl                      true
% 7.26/1.48  --gc_record_bc_elim                     false
% 7.26/1.48  
% 7.26/1.48  ------ Preprocessing Options
% 7.26/1.48  
% 7.26/1.48  --preprocessing_flag                    true
% 7.26/1.48  --time_out_prep_mult                    0.1
% 7.26/1.48  --splitting_mode                        input
% 7.26/1.48  --splitting_grd                         true
% 7.26/1.48  --splitting_cvd                         false
% 7.26/1.48  --splitting_cvd_svl                     false
% 7.26/1.48  --splitting_nvd                         32
% 7.26/1.48  --sub_typing                            true
% 7.26/1.48  --prep_gs_sim                           true
% 7.26/1.48  --prep_unflatten                        true
% 7.26/1.48  --prep_res_sim                          true
% 7.26/1.48  --prep_upred                            true
% 7.26/1.48  --prep_sem_filter                       exhaustive
% 7.26/1.48  --prep_sem_filter_out                   false
% 7.26/1.48  --pred_elim                             true
% 7.26/1.48  --res_sim_input                         true
% 7.26/1.48  --eq_ax_congr_red                       true
% 7.26/1.48  --pure_diseq_elim                       true
% 7.26/1.48  --brand_transform                       false
% 7.26/1.48  --non_eq_to_eq                          false
% 7.26/1.48  --prep_def_merge                        true
% 7.26/1.48  --prep_def_merge_prop_impl              false
% 7.26/1.48  --prep_def_merge_mbd                    true
% 7.26/1.48  --prep_def_merge_tr_red                 false
% 7.26/1.48  --prep_def_merge_tr_cl                  false
% 7.26/1.48  --smt_preprocessing                     true
% 7.26/1.48  --smt_ac_axioms                         fast
% 7.26/1.48  --preprocessed_out                      false
% 7.26/1.48  --preprocessed_stats                    false
% 7.26/1.48  
% 7.26/1.48  ------ Abstraction refinement Options
% 7.26/1.48  
% 7.26/1.48  --abstr_ref                             []
% 7.26/1.48  --abstr_ref_prep                        false
% 7.26/1.48  --abstr_ref_until_sat                   false
% 7.26/1.48  --abstr_ref_sig_restrict                funpre
% 7.26/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.48  --abstr_ref_under                       []
% 7.26/1.48  
% 7.26/1.48  ------ SAT Options
% 7.26/1.48  
% 7.26/1.48  --sat_mode                              false
% 7.26/1.48  --sat_fm_restart_options                ""
% 7.26/1.48  --sat_gr_def                            false
% 7.26/1.48  --sat_epr_types                         true
% 7.26/1.48  --sat_non_cyclic_types                  false
% 7.26/1.48  --sat_finite_models                     false
% 7.26/1.48  --sat_fm_lemmas                         false
% 7.26/1.48  --sat_fm_prep                           false
% 7.26/1.48  --sat_fm_uc_incr                        true
% 7.26/1.48  --sat_out_model                         small
% 7.26/1.48  --sat_out_clauses                       false
% 7.26/1.48  
% 7.26/1.48  ------ QBF Options
% 7.26/1.48  
% 7.26/1.48  --qbf_mode                              false
% 7.26/1.48  --qbf_elim_univ                         false
% 7.26/1.48  --qbf_dom_inst                          none
% 7.26/1.48  --qbf_dom_pre_inst                      false
% 7.26/1.48  --qbf_sk_in                             false
% 7.26/1.48  --qbf_pred_elim                         true
% 7.26/1.48  --qbf_split                             512
% 7.26/1.48  
% 7.26/1.48  ------ BMC1 Options
% 7.26/1.48  
% 7.26/1.48  --bmc1_incremental                      false
% 7.26/1.48  --bmc1_axioms                           reachable_all
% 7.26/1.48  --bmc1_min_bound                        0
% 7.26/1.48  --bmc1_max_bound                        -1
% 7.26/1.48  --bmc1_max_bound_default                -1
% 7.26/1.48  --bmc1_symbol_reachability              true
% 7.26/1.48  --bmc1_property_lemmas                  false
% 7.26/1.48  --bmc1_k_induction                      false
% 7.26/1.48  --bmc1_non_equiv_states                 false
% 7.26/1.48  --bmc1_deadlock                         false
% 7.26/1.48  --bmc1_ucm                              false
% 7.26/1.48  --bmc1_add_unsat_core                   none
% 7.26/1.48  --bmc1_unsat_core_children              false
% 7.26/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.48  --bmc1_out_stat                         full
% 7.26/1.48  --bmc1_ground_init                      false
% 7.26/1.48  --bmc1_pre_inst_next_state              false
% 7.26/1.48  --bmc1_pre_inst_state                   false
% 7.26/1.48  --bmc1_pre_inst_reach_state             false
% 7.26/1.48  --bmc1_out_unsat_core                   false
% 7.26/1.48  --bmc1_aig_witness_out                  false
% 7.26/1.48  --bmc1_verbose                          false
% 7.26/1.48  --bmc1_dump_clauses_tptp                false
% 7.26/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.48  --bmc1_dump_file                        -
% 7.26/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.48  --bmc1_ucm_extend_mode                  1
% 7.26/1.48  --bmc1_ucm_init_mode                    2
% 7.26/1.48  --bmc1_ucm_cone_mode                    none
% 7.26/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.48  --bmc1_ucm_relax_model                  4
% 7.26/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.48  --bmc1_ucm_layered_model                none
% 7.26/1.48  --bmc1_ucm_max_lemma_size               10
% 7.26/1.48  
% 7.26/1.48  ------ AIG Options
% 7.26/1.48  
% 7.26/1.48  --aig_mode                              false
% 7.26/1.48  
% 7.26/1.48  ------ Instantiation Options
% 7.26/1.48  
% 7.26/1.48  --instantiation_flag                    true
% 7.26/1.48  --inst_sos_flag                         true
% 7.26/1.48  --inst_sos_phase                        true
% 7.26/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.48  --inst_lit_sel_side                     none
% 7.26/1.48  --inst_solver_per_active                1400
% 7.26/1.48  --inst_solver_calls_frac                1.
% 7.26/1.48  --inst_passive_queue_type               priority_queues
% 7.26/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.48  --inst_passive_queues_freq              [25;2]
% 7.26/1.48  --inst_dismatching                      true
% 7.26/1.48  --inst_eager_unprocessed_to_passive     true
% 7.26/1.49  --inst_prop_sim_given                   true
% 7.26/1.49  --inst_prop_sim_new                     false
% 7.26/1.49  --inst_subs_new                         false
% 7.26/1.49  --inst_eq_res_simp                      false
% 7.26/1.49  --inst_subs_given                       false
% 7.26/1.49  --inst_orphan_elimination               true
% 7.26/1.49  --inst_learning_loop_flag               true
% 7.26/1.49  --inst_learning_start                   3000
% 7.26/1.49  --inst_learning_factor                  2
% 7.26/1.49  --inst_start_prop_sim_after_learn       3
% 7.26/1.49  --inst_sel_renew                        solver
% 7.26/1.49  --inst_lit_activity_flag                true
% 7.26/1.49  --inst_restr_to_given                   false
% 7.26/1.49  --inst_activity_threshold               500
% 7.26/1.49  --inst_out_proof                        true
% 7.26/1.49  
% 7.26/1.49  ------ Resolution Options
% 7.26/1.49  
% 7.26/1.49  --resolution_flag                       false
% 7.26/1.49  --res_lit_sel                           adaptive
% 7.26/1.49  --res_lit_sel_side                      none
% 7.26/1.49  --res_ordering                          kbo
% 7.26/1.49  --res_to_prop_solver                    active
% 7.26/1.49  --res_prop_simpl_new                    false
% 7.26/1.49  --res_prop_simpl_given                  true
% 7.26/1.49  --res_passive_queue_type                priority_queues
% 7.26/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.49  --res_passive_queues_freq               [15;5]
% 7.26/1.49  --res_forward_subs                      full
% 7.26/1.49  --res_backward_subs                     full
% 7.26/1.49  --res_forward_subs_resolution           true
% 7.26/1.49  --res_backward_subs_resolution          true
% 7.26/1.49  --res_orphan_elimination                true
% 7.26/1.49  --res_time_limit                        2.
% 7.26/1.49  --res_out_proof                         true
% 7.26/1.49  
% 7.26/1.49  ------ Superposition Options
% 7.26/1.49  
% 7.26/1.49  --superposition_flag                    true
% 7.26/1.49  --sup_passive_queue_type                priority_queues
% 7.26/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.49  --demod_completeness_check              fast
% 7.26/1.49  --demod_use_ground                      true
% 7.26/1.49  --sup_to_prop_solver                    passive
% 7.26/1.49  --sup_prop_simpl_new                    true
% 7.26/1.49  --sup_prop_simpl_given                  true
% 7.26/1.49  --sup_fun_splitting                     true
% 7.26/1.49  --sup_smt_interval                      50000
% 7.26/1.49  
% 7.26/1.49  ------ Superposition Simplification Setup
% 7.26/1.49  
% 7.26/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.26/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.26/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.26/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.26/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.26/1.49  --sup_immed_triv                        [TrivRules]
% 7.26/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.49  --sup_immed_bw_main                     []
% 7.26/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.26/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.49  --sup_input_bw                          []
% 7.26/1.49  
% 7.26/1.49  ------ Combination Options
% 7.26/1.49  
% 7.26/1.49  --comb_res_mult                         3
% 7.26/1.49  --comb_sup_mult                         2
% 7.26/1.49  --comb_inst_mult                        10
% 7.26/1.49  
% 7.26/1.49  ------ Debug Options
% 7.26/1.49  
% 7.26/1.49  --dbg_backtrace                         false
% 7.26/1.49  --dbg_dump_prop_clauses                 false
% 7.26/1.49  --dbg_dump_prop_clauses_file            -
% 7.26/1.49  --dbg_out_stat                          false
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  ------ Proving...
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  % SZS status Theorem for theBenchmark.p
% 7.26/1.49  
% 7.26/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.49  
% 7.26/1.49  fof(f22,axiom,(
% 7.26/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f52,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f22])).
% 7.26/1.49  
% 7.26/1.49  fof(f53,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f52])).
% 7.26/1.49  
% 7.26/1.49  fof(f68,plain,(
% 7.26/1.49    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f69,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f68])).
% 7.26/1.49  
% 7.26/1.49  fof(f114,plain,(
% 7.26/1.49    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f69])).
% 7.26/1.49  
% 7.26/1.49  fof(f23,conjecture,(
% 7.26/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f24,negated_conjecture,(
% 7.26/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 7.26/1.49    inference(negated_conjecture,[],[f23])).
% 7.26/1.49  
% 7.26/1.49  fof(f54,plain,(
% 7.26/1.49    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f24])).
% 7.26/1.49  
% 7.26/1.49  fof(f55,plain,(
% 7.26/1.49    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f54])).
% 7.26/1.49  
% 7.26/1.49  fof(f70,plain,(
% 7.26/1.49    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.26/1.49    inference(nnf_transformation,[],[f55])).
% 7.26/1.49  
% 7.26/1.49  fof(f71,plain,(
% 7.26/1.49    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f70])).
% 7.26/1.49  
% 7.26/1.49  fof(f73,plain,(
% 7.26/1.49    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f72,plain,(
% 7.26/1.49    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f74,plain,(
% 7.26/1.49    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f71,f73,f72])).
% 7.26/1.49  
% 7.26/1.49  fof(f121,plain,(
% 7.26/1.49    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  fof(f115,plain,(
% 7.26/1.49    ~v2_struct_0(sK3)),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  fof(f116,plain,(
% 7.26/1.49    v2_pre_topc(sK3)),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  fof(f118,plain,(
% 7.26/1.49    l1_pre_topc(sK3)),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  fof(f119,plain,(
% 7.26/1.49    ~v1_xboole_0(sK4)),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  fof(f120,plain,(
% 7.26/1.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  fof(f2,axiom,(
% 7.26/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f25,plain,(
% 7.26/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f2])).
% 7.26/1.49  
% 7.26/1.49  fof(f60,plain,(
% 7.26/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.49    inference(nnf_transformation,[],[f25])).
% 7.26/1.49  
% 7.26/1.49  fof(f61,plain,(
% 7.26/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.49    inference(rectify,[],[f60])).
% 7.26/1.49  
% 7.26/1.49  fof(f62,plain,(
% 7.26/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f63,plain,(
% 7.26/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f61,f62])).
% 7.26/1.49  
% 7.26/1.49  fof(f78,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f63])).
% 7.26/1.49  
% 7.26/1.49  fof(f6,axiom,(
% 7.26/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f26,plain,(
% 7.26/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.26/1.49    inference(ennf_transformation,[],[f6])).
% 7.26/1.49  
% 7.26/1.49  fof(f84,plain,(
% 7.26/1.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f26])).
% 7.26/1.49  
% 7.26/1.49  fof(f12,axiom,(
% 7.26/1.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f33,plain,(
% 7.26/1.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f12])).
% 7.26/1.49  
% 7.26/1.49  fof(f34,plain,(
% 7.26/1.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.26/1.49    inference(flattening,[],[f33])).
% 7.26/1.49  
% 7.26/1.49  fof(f91,plain,(
% 7.26/1.49    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f34])).
% 7.26/1.49  
% 7.26/1.49  fof(f3,axiom,(
% 7.26/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f80,plain,(
% 7.26/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f3])).
% 7.26/1.49  
% 7.26/1.49  fof(f126,plain,(
% 7.26/1.49    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.26/1.49    inference(definition_unfolding,[],[f91,f80])).
% 7.26/1.49  
% 7.26/1.49  fof(f1,axiom,(
% 7.26/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f56,plain,(
% 7.26/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.49    inference(nnf_transformation,[],[f1])).
% 7.26/1.49  
% 7.26/1.49  fof(f57,plain,(
% 7.26/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.49    inference(rectify,[],[f56])).
% 7.26/1.49  
% 7.26/1.49  fof(f58,plain,(
% 7.26/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f59,plain,(
% 7.26/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).
% 7.26/1.49  
% 7.26/1.49  fof(f75,plain,(
% 7.26/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f59])).
% 7.26/1.49  
% 7.26/1.49  fof(f76,plain,(
% 7.26/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f59])).
% 7.26/1.49  
% 7.26/1.49  fof(f5,axiom,(
% 7.26/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f64,plain,(
% 7.26/1.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.26/1.49    inference(nnf_transformation,[],[f5])).
% 7.26/1.49  
% 7.26/1.49  fof(f82,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f64])).
% 7.26/1.49  
% 7.26/1.49  fof(f125,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 7.26/1.49    inference(definition_unfolding,[],[f82,f80])).
% 7.26/1.49  
% 7.26/1.49  fof(f83,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f64])).
% 7.26/1.49  
% 7.26/1.49  fof(f124,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.26/1.49    inference(definition_unfolding,[],[f83,f80])).
% 7.26/1.49  
% 7.26/1.49  fof(f20,axiom,(
% 7.26/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f48,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 7.26/1.49    inference(ennf_transformation,[],[f20])).
% 7.26/1.49  
% 7.26/1.49  fof(f49,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.26/1.49    inference(flattening,[],[f48])).
% 7.26/1.49  
% 7.26/1.49  fof(f107,plain,(
% 7.26/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f49])).
% 7.26/1.49  
% 7.26/1.49  fof(f4,axiom,(
% 7.26/1.49    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f81,plain,(
% 7.26/1.49    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 7.26/1.49    inference(cnf_transformation,[],[f4])).
% 7.26/1.49  
% 7.26/1.49  fof(f123,plain,(
% 7.26/1.49    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 7.26/1.49    inference(definition_unfolding,[],[f81,f80])).
% 7.26/1.49  
% 7.26/1.49  fof(f7,axiom,(
% 7.26/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f65,plain,(
% 7.26/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.26/1.49    inference(nnf_transformation,[],[f7])).
% 7.26/1.49  
% 7.26/1.49  fof(f85,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.26/1.49    inference(cnf_transformation,[],[f65])).
% 7.26/1.49  
% 7.26/1.49  fof(f77,plain,(
% 7.26/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f63])).
% 7.26/1.49  
% 7.26/1.49  fof(f18,axiom,(
% 7.26/1.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f44,plain,(
% 7.26/1.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f18])).
% 7.26/1.49  
% 7.26/1.49  fof(f45,plain,(
% 7.26/1.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f44])).
% 7.26/1.49  
% 7.26/1.49  fof(f103,plain,(
% 7.26/1.49    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f45])).
% 7.26/1.49  
% 7.26/1.49  fof(f79,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f63])).
% 7.26/1.49  
% 7.26/1.49  fof(f19,axiom,(
% 7.26/1.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f46,plain,(
% 7.26/1.49    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f19])).
% 7.26/1.49  
% 7.26/1.49  fof(f47,plain,(
% 7.26/1.49    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f46])).
% 7.26/1.49  
% 7.26/1.49  fof(f104,plain,(
% 7.26/1.49    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f47])).
% 7.26/1.49  
% 7.26/1.49  fof(f105,plain,(
% 7.26/1.49    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f47])).
% 7.26/1.49  
% 7.26/1.49  fof(f17,axiom,(
% 7.26/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f42,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f17])).
% 7.26/1.49  
% 7.26/1.49  fof(f43,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f42])).
% 7.26/1.49  
% 7.26/1.49  fof(f66,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(nnf_transformation,[],[f43])).
% 7.26/1.49  
% 7.26/1.49  fof(f99,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f66])).
% 7.26/1.49  
% 7.26/1.49  fof(f127,plain,(
% 7.26/1.49    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(equality_resolution,[],[f99])).
% 7.26/1.49  
% 7.26/1.49  fof(f106,plain,(
% 7.26/1.49    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f47])).
% 7.26/1.49  
% 7.26/1.49  fof(f21,axiom,(
% 7.26/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f50,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f21])).
% 7.26/1.49  
% 7.26/1.49  fof(f51,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f50])).
% 7.26/1.49  
% 7.26/1.49  fof(f67,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(nnf_transformation,[],[f51])).
% 7.26/1.49  
% 7.26/1.49  fof(f109,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f67])).
% 7.26/1.49  
% 7.26/1.49  fof(f128,plain,(
% 7.26/1.49    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(equality_resolution,[],[f109])).
% 7.26/1.49  
% 7.26/1.49  fof(f13,axiom,(
% 7.26/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f35,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.26/1.49    inference(ennf_transformation,[],[f13])).
% 7.26/1.49  
% 7.26/1.49  fof(f92,plain,(
% 7.26/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f35])).
% 7.26/1.49  
% 7.26/1.49  fof(f122,plain,(
% 7.26/1.49    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  fof(f8,axiom,(
% 7.26/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f27,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f8])).
% 7.26/1.49  
% 7.26/1.49  fof(f28,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.26/1.49    inference(flattening,[],[f27])).
% 7.26/1.49  
% 7.26/1.49  fof(f87,plain,(
% 7.26/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f28])).
% 7.26/1.49  
% 7.26/1.49  fof(f14,axiom,(
% 7.26/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f36,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f14])).
% 7.26/1.49  
% 7.26/1.49  fof(f37,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f36])).
% 7.26/1.49  
% 7.26/1.49  fof(f94,plain,(
% 7.26/1.49    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f37])).
% 7.26/1.49  
% 7.26/1.49  fof(f9,axiom,(
% 7.26/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f29,plain,(
% 7.26/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.26/1.49    inference(ennf_transformation,[],[f9])).
% 7.26/1.49  
% 7.26/1.49  fof(f88,plain,(
% 7.26/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f29])).
% 7.26/1.49  
% 7.26/1.49  fof(f11,axiom,(
% 7.26/1.49    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f31,plain,(
% 7.26/1.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f11])).
% 7.26/1.49  
% 7.26/1.49  fof(f32,plain,(
% 7.26/1.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f31])).
% 7.26/1.49  
% 7.26/1.49  fof(f90,plain,(
% 7.26/1.49    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f32])).
% 7.26/1.49  
% 7.26/1.49  fof(f113,plain,(
% 7.26/1.49    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f69])).
% 7.26/1.49  
% 7.26/1.49  fof(f16,axiom,(
% 7.26/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f40,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f16])).
% 7.26/1.49  
% 7.26/1.49  fof(f41,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.26/1.49    inference(flattening,[],[f40])).
% 7.26/1.49  
% 7.26/1.49  fof(f98,plain,(
% 7.26/1.49    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f41])).
% 7.26/1.49  
% 7.26/1.49  fof(f10,axiom,(
% 7.26/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f30,plain,(
% 7.26/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.26/1.49    inference(ennf_transformation,[],[f10])).
% 7.26/1.49  
% 7.26/1.49  fof(f89,plain,(
% 7.26/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f30])).
% 7.26/1.49  
% 7.26/1.49  fof(f112,plain,(
% 7.26/1.49    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f69])).
% 7.26/1.49  
% 7.26/1.49  fof(f110,plain,(
% 7.26/1.49    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f69])).
% 7.26/1.49  
% 7.26/1.49  fof(f117,plain,(
% 7.26/1.49    v2_tdlat_3(sK3)),
% 7.26/1.49    inference(cnf_transformation,[],[f74])).
% 7.26/1.49  
% 7.26/1.49  cnf(c_34,plain,
% 7.26/1.49      ( ~ v2_tex_2(X0,X1)
% 7.26/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v1_xboole_0(X0)
% 7.26/1.49      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 7.26/1.49      inference(cnf_transformation,[],[f114]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_40,negated_conjecture,
% 7.26/1.49      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_382,plain,
% 7.26/1.49      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 7.26/1.49      inference(prop_impl,[status(thm)],[c_40]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_383,plain,
% 7.26/1.49      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_382]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1837,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v1_xboole_0(X0)
% 7.26/1.49      | u1_struct_0(sK2(X1,X0)) = X0
% 7.26/1.49      | sK3 != X1
% 7.26/1.49      | sK4 != X0 ),
% 7.26/1.49      inference(resolution_lifted,[status(thm)],[c_34,c_383]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1838,plain,
% 7.26/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | ~ v2_pre_topc(sK3)
% 7.26/1.49      | v1_xboole_0(sK4)
% 7.26/1.49      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 7.26/1.49      inference(unflattening,[status(thm)],[c_1837]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_46,negated_conjecture,
% 7.26/1.49      ( ~ v2_struct_0(sK3) ),
% 7.26/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_45,negated_conjecture,
% 7.26/1.49      ( v2_pre_topc(sK3) ),
% 7.26/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_43,negated_conjecture,
% 7.26/1.49      ( l1_pre_topc(sK3) ),
% 7.26/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_42,negated_conjecture,
% 7.26/1.49      ( ~ v1_xboole_0(sK4) ),
% 7.26/1.49      inference(cnf_transformation,[],[f119]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_41,negated_conjecture,
% 7.26/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.26/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1840,plain,
% 7.26/1.49      ( v1_zfmisc_1(sK4) | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_1838,c_46,c_45,c_43,c_42,c_41]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6354,plain,
% 7.26/1.49      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 7.26/1.49      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_1840]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_3,plain,
% 7.26/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6395,plain,
% 7.26/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.26/1.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_8,plain,
% 7.26/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6390,plain,
% 7.26/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.26/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6958,plain,
% 7.26/1.49      ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 7.26/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6395,c_6390]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_15,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,X1)
% 7.26/1.49      | v1_xboole_0(X1)
% 7.26/1.49      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6385,plain,
% 7.26/1.49      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 7.26/1.49      | m1_subset_1(X1,X0) != iProver_top
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9087,plain,
% 7.26/1.49      ( k2_tarski(sK1(X0,X1),sK1(X0,X1)) = k6_domain_1(X0,sK1(X0,X1))
% 7.26/1.49      | r1_tarski(X0,X1) = iProver_top
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6958,c_6385]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1,plain,
% 7.26/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6397,plain,
% 7.26/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.26/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6957,plain,
% 7.26/1.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6395,c_6397]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21535,plain,
% 7.26/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.26/1.49      | k2_tarski(sK1(X0,X1),sK1(X0,X1)) = k6_domain_1(X0,sK1(X0,X1)) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_9087,c_6957]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21536,plain,
% 7.26/1.49      ( k2_tarski(sK1(X0,X1),sK1(X0,X1)) = k6_domain_1(X0,sK1(X0,X1))
% 7.26/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_21535]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_0,plain,
% 7.26/1.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6398,plain,
% 7.26/1.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6741,plain,
% 7.26/1.49      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6398,c_6390]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_8648,plain,
% 7.26/1.49      ( k2_tarski(sK0(X0),sK0(X0)) = k6_domain_1(X0,sK0(X0))
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6741,c_6385]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6372,plain,
% 7.26/1.49      ( v1_xboole_0(sK4) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9181,plain,
% 7.26/1.49      ( k2_tarski(sK0(sK4),sK0(sK4)) = k6_domain_1(sK4,sK0(sK4)) ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_8648,c_6372]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7,plain,
% 7.26/1.49      ( ~ r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6391,plain,
% 7.26/1.49      ( r1_tarski(k2_tarski(X0,X0),X1) != iProver_top
% 7.26/1.49      | r2_hidden(X0,X1) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9197,plain,
% 7.26/1.49      ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),X0) != iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),X0) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_9181,c_6391]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21544,plain,
% 7.26/1.49      ( k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),X0),sK1(k6_domain_1(sK4,sK0(sK4)),X0)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),X0))
% 7.26/1.49      | r2_hidden(sK0(sK4),X0) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_21536,c_9197]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6,plain,
% 7.26/1.49      ( r1_tarski(k2_tarski(X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6392,plain,
% 7.26/1.49      ( r1_tarski(k2_tarski(X0,X0),X1) = iProver_top
% 7.26/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_31,plain,
% 7.26/1.49      ( ~ r1_tarski(X0,X1)
% 7.26/1.49      | ~ v1_zfmisc_1(X1)
% 7.26/1.49      | v1_xboole_0(X0)
% 7.26/1.49      | v1_xboole_0(X1)
% 7.26/1.49      | X1 = X0 ),
% 7.26/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6374,plain,
% 7.26/1.49      ( X0 = X1
% 7.26/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(X0) != iProver_top
% 7.26/1.49      | v1_xboole_0(X1) = iProver_top
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7880,plain,
% 7.26/1.49      ( k2_tarski(X0,X0) = X1
% 7.26/1.49      | r2_hidden(X0,X1) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(X1) != iProver_top
% 7.26/1.49      | v1_xboole_0(X1) = iProver_top
% 7.26/1.49      | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6392,c_6374]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_5,plain,
% 7.26/1.49      ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
% 7.26/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_138,plain,
% 7.26/1.49      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_148,plain,
% 7.26/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.26/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_17673,plain,
% 7.26/1.49      ( k2_tarski(X0,X0) = X1
% 7.26/1.49      | r2_hidden(X0,X1) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(X1) != iProver_top ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_7880,c_138,c_148]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21578,plain,
% 7.26/1.49      ( k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),X0),sK1(k6_domain_1(sK4,sK0(sK4)),X0)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),X0))
% 7.26/1.49      | k2_tarski(sK0(sK4),sK0(sK4)) = X0
% 7.26/1.49      | v1_zfmisc_1(X0) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_21544,c_17673]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21598,plain,
% 7.26/1.49      ( k6_domain_1(sK4,sK0(sK4)) = X0
% 7.26/1.49      | k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),X0),sK1(k6_domain_1(sK4,sK0(sK4)),X0)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),X0))
% 7.26/1.49      | v1_zfmisc_1(X0) != iProver_top ),
% 7.26/1.49      inference(demodulation,[status(thm)],[c_21578,c_9181]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21657,plain,
% 7.26/1.49      ( k6_domain_1(sK4,sK0(sK4)) = sK4
% 7.26/1.49      | k2_tarski(sK1(k6_domain_1(sK4,sK0(sK4)),sK4),sK1(k6_domain_1(sK4,sK0(sK4)),sK4)) = k6_domain_1(k6_domain_1(sK4,sK0(sK4)),sK1(k6_domain_1(sK4,sK0(sK4)),sK4))
% 7.26/1.49      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6354,c_21598]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6373,plain,
% 7.26/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_10,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6388,plain,
% 7.26/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6791,plain,
% 7.26/1.49      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6373,c_6388]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6792,plain,
% 7.26/1.49      ( r1_tarski(sK4,u1_struct_0(sK3)) ),
% 7.26/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_6791]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7961,plain,
% 7.26/1.49      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_4,plain,
% 7.26/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6588,plain,
% 7.26/1.49      ( ~ r1_tarski(X0,u1_struct_0(sK3))
% 7.26/1.49      | ~ r2_hidden(X1,X0)
% 7.26/1.49      | r2_hidden(X1,u1_struct_0(sK3)) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_8720,plain,
% 7.26/1.49      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 7.26/1.49      | r2_hidden(sK0(sK4),u1_struct_0(sK3))
% 7.26/1.49      | ~ r2_hidden(sK0(sK4),sK4) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_6588]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6521,plain,
% 7.26/1.49      ( m1_subset_1(X0,u1_struct_0(sK3))
% 7.26/1.49      | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9851,plain,
% 7.26/1.49      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3))
% 7.26/1.49      | ~ r2_hidden(sK0(sK4),u1_struct_0(sK3)) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_6521]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_25,plain,
% 7.26/1.49      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 7.26/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | ~ l1_pre_topc(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6461,plain,
% 7.26/1.49      ( m1_pre_topc(k1_tex_2(sK3,X0),sK3)
% 7.26/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | ~ l1_pre_topc(sK3) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_10466,plain,
% 7.26/1.49      ( m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3)
% 7.26/1.49      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | ~ l1_pre_topc(sK3) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_6461]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9196,plain,
% 7.26/1.49      ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),X0) = iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),X0) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_9181,c_6392]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6394,plain,
% 7.26/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.26/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9280,plain,
% 7.26/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.26/1.49      | r2_hidden(X0,k6_domain_1(sK4,sK0(sK4))) != iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),X1) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_9196,c_6394]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9647,plain,
% 7.26/1.49      ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),X0) = iProver_top
% 7.26/1.49      | r2_hidden(sK1(k6_domain_1(sK4,sK0(sK4)),X0),X1) = iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),X1) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6395,c_9280]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7299,plain,
% 7.26/1.49      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 7.26/1.49      | r2_hidden(X0,sK4) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6791,c_6394]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_2,plain,
% 7.26/1.49      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6396,plain,
% 7.26/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.26/1.49      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7320,plain,
% 7.26/1.49      ( r1_tarski(X0,u1_struct_0(sK3)) = iProver_top
% 7.26/1.49      | r2_hidden(sK1(X0,u1_struct_0(sK3)),sK4) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_7299,c_6396]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_11317,plain,
% 7.26/1.49      ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),u1_struct_0(sK3)) = iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_9647,c_7320]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_51,plain,
% 7.26/1.49      ( v1_xboole_0(sK4) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7962,plain,
% 7.26/1.49      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 7.26/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_7961]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_11501,plain,
% 7.26/1.49      ( r1_tarski(k6_domain_1(sK4,sK0(sK4)),u1_struct_0(sK3)) = iProver_top ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_11317,c_51,c_7962]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_11507,plain,
% 7.26/1.49      ( r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_11501,c_9197]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_12068,plain,
% 7.26/1.49      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_11507,c_6390]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_30,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 7.26/1.49      | ~ l1_pre_topc(X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6376,plain,
% 7.26/1.49      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.26/1.49      | v2_struct_0(X1) = iProver_top
% 7.26/1.49      | v2_struct_0(k1_tex_2(X1,X0)) != iProver_top
% 7.26/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_12072,plain,
% 7.26/1.49      ( v2_struct_0(k1_tex_2(sK3,sK0(sK4))) != iProver_top
% 7.26/1.49      | v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_12068,c_6376]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_12077,plain,
% 7.26/1.49      ( ~ v2_struct_0(k1_tex_2(sK3,sK0(sK4)))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | ~ l1_pre_topc(sK3) ),
% 7.26/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_12072]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_29,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v7_struct_0(k1_tex_2(X1,X0))
% 7.26/1.49      | ~ l1_pre_topc(X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6375,plain,
% 7.26/1.49      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.26/1.49      | v2_struct_0(X1) = iProver_top
% 7.26/1.49      | v7_struct_0(k1_tex_2(X1,X0)) = iProver_top
% 7.26/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_12074,plain,
% 7.26/1.49      ( v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | v7_struct_0(k1_tex_2(sK3,sK0(sK4))) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_12068,c_6375]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_12079,plain,
% 7.26/1.49      ( v2_struct_0(sK3)
% 7.26/1.49      | v7_struct_0(k1_tex_2(sK3,sK0(sK4)))
% 7.26/1.49      | ~ l1_pre_topc(sK3) ),
% 7.26/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_12074]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_24,plain,
% 7.26/1.49      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
% 7.26/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.26/1.49      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | v2_struct_0(k1_tex_2(X0,X1))
% 7.26/1.49      | ~ l1_pre_topc(X0)
% 7.26/1.49      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 7.26/1.49      inference(cnf_transformation,[],[f127]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_283,plain,
% 7.26/1.49      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.26/1.49      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | v2_struct_0(k1_tex_2(X0,X1))
% 7.26/1.49      | ~ l1_pre_topc(X0)
% 7.26/1.49      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_24,c_25]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_284,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.26/1.49      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v2_struct_0(k1_tex_2(X1,X0))
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_283]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_28,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.26/1.49      | v1_pre_topc(k1_tex_2(X1,X0))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ l1_pre_topc(X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_289,plain,
% 7.26/1.49      ( v2_struct_0(X1)
% 7.26/1.49      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_284,c_30,c_28]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_290,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_289]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6367,plain,
% 7.26/1.49      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
% 7.26/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.26/1.49      | v2_struct_0(X0) = iProver_top
% 7.26/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_13261,plain,
% 7.26/1.49      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = u1_struct_0(k1_tex_2(sK3,sK0(sK4)))
% 7.26/1.49      | v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_12068,c_6367]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7319,plain,
% 7.26/1.49      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 7.26/1.49      | r2_hidden(X0,sK4) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_7299,c_6390]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7524,plain,
% 7.26/1.49      ( k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0)
% 7.26/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.26/1.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_7319,c_6385]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7318,plain,
% 7.26/1.49      ( r2_hidden(X0,sK4) != iProver_top
% 7.26/1.49      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_7299,c_6397]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7669,plain,
% 7.26/1.49      ( r2_hidden(X0,sK4) != iProver_top
% 7.26/1.49      | k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_7524,c_7318]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7670,plain,
% 7.26/1.49      ( k6_domain_1(u1_struct_0(sK3),X0) = k2_tarski(X0,X0)
% 7.26/1.49      | r2_hidden(X0,sK4) != iProver_top ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_7669]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7675,plain,
% 7.26/1.49      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k2_tarski(sK0(sK4),sK0(sK4))
% 7.26/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6398,c_7670]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7807,plain,
% 7.26/1.49      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k2_tarski(sK0(sK4),sK0(sK4)) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_7675,c_51]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9190,plain,
% 7.26/1.49      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k6_domain_1(sK4,sK0(sK4)) ),
% 7.26/1.49      inference(demodulation,[status(thm)],[c_9181,c_7807]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_13264,plain,
% 7.26/1.49      ( u1_struct_0(k1_tex_2(sK3,sK0(sK4))) = k6_domain_1(sK4,sK0(sK4))
% 7.26/1.49      | v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(light_normalisation,[status(thm)],[c_13261,c_9190]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_47,plain,
% 7.26/1.49      ( v2_struct_0(sK3) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_50,plain,
% 7.26/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_13544,plain,
% 7.26/1.49      ( u1_struct_0(k1_tex_2(sK3,sK0(sK4))) = k6_domain_1(sK4,sK0(sK4)) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_13264,c_47,c_50]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_32,plain,
% 7.26/1.49      ( v2_tex_2(u1_struct_0(X0),X1)
% 7.26/1.49      | ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | ~ l1_pre_topc(X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f128]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_16,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | ~ l1_pre_topc(X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_269,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | v2_tex_2(u1_struct_0(X0),X1)
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | ~ l1_pre_topc(X1) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_32,c_16]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_270,plain,
% 7.26/1.49      ( v2_tex_2(u1_struct_0(X0),X1)
% 7.26/1.49      | ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ l1_pre_topc(X1) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_269]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_39,negated_conjecture,
% 7.26/1.49      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(cnf_transformation,[],[f122]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_380,plain,
% 7.26/1.49      ( ~ v1_zfmisc_1(sK4) | ~ v2_tex_2(sK4,sK3) ),
% 7.26/1.49      inference(prop_impl,[status(thm)],[c_39]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_381,plain,
% 7.26/1.49      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_380]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1727,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | u1_struct_0(X0) != sK4
% 7.26/1.49      | sK3 != X1 ),
% 7.26/1.49      inference(resolution_lifted,[status(thm)],[c_270,c_381]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1728,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,sK3)
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | ~ v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | u1_struct_0(X0) != sK4 ),
% 7.26/1.49      inference(unflattening,[status(thm)],[c_1727]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1732,plain,
% 7.26/1.49      ( ~ v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ m1_pre_topc(X0,sK3)
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | u1_struct_0(X0) != sK4 ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_1728,c_46,c_43]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1733,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,sK3)
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | ~ v1_zfmisc_1(sK4)
% 7.26/1.49      | u1_struct_0(X0) != sK4 ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_1732]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6360,plain,
% 7.26/1.49      ( u1_struct_0(X0) != sK4
% 7.26/1.49      | m1_pre_topc(X0,sK3) != iProver_top
% 7.26/1.49      | v1_tdlat_3(X0) != iProver_top
% 7.26/1.49      | v2_struct_0(X0) = iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_1733]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_13553,plain,
% 7.26/1.49      ( k6_domain_1(sK4,sK0(sK4)) != sK4
% 7.26/1.49      | m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3) != iProver_top
% 7.26/1.49      | v1_tdlat_3(k1_tex_2(sK3,sK0(sK4))) != iProver_top
% 7.26/1.49      | v2_struct_0(k1_tex_2(sK3,sK0(sK4))) = iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_13544,c_6360]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_8721,plain,
% 7.26/1.49      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_8720]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9281,plain,
% 7.26/1.49      ( k6_domain_1(sK4,sK0(sK4)) = X0
% 7.26/1.49      | r2_hidden(sK0(sK4),X0) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(X0) != iProver_top
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top
% 7.26/1.49      | v1_xboole_0(k6_domain_1(sK4,sK0(sK4))) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_9196,c_6374]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6393,plain,
% 7.26/1.49      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9198,plain,
% 7.26/1.49      ( v1_xboole_0(k6_domain_1(sK4,sK0(sK4))) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_9181,c_6393]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9820,plain,
% 7.26/1.49      ( v1_xboole_0(X0) = iProver_top
% 7.26/1.49      | v1_zfmisc_1(X0) != iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),X0) != iProver_top
% 7.26/1.49      | k6_domain_1(sK4,sK0(sK4)) = X0 ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_9281,c_9198]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9821,plain,
% 7.26/1.49      ( k6_domain_1(sK4,sK0(sK4)) = X0
% 7.26/1.49      | r2_hidden(sK0(sK4),X0) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(X0) != iProver_top
% 7.26/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_9820]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9826,plain,
% 7.26/1.49      ( k6_domain_1(sK4,sK0(sK4)) = sK4
% 7.26/1.49      | v1_zfmisc_1(sK4) != iProver_top
% 7.26/1.49      | v1_xboole_0(sK4) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6398,c_9821]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9852,plain,
% 7.26/1.49      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 7.26/1.49      | r2_hidden(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_9851]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_10467,plain,
% 7.26/1.49      ( m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3) = iProver_top
% 7.26/1.49      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.26/1.49      | v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_10466]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_16283,plain,
% 7.26/1.49      ( v1_tdlat_3(k1_tex_2(sK3,sK0(sK4))) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) != iProver_top ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_13553,c_47,c_50,c_51,c_6791,c_7962,c_8721,c_9826,
% 7.26/1.49                 c_9852,c_10467,c_12072]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_16285,plain,
% 7.26/1.49      ( ~ v1_tdlat_3(k1_tex_2(sK3,sK0(sK4))) | ~ v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_16283]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6378,plain,
% 7.26/1.49      ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
% 7.26/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.26/1.49      | v2_struct_0(X0) = iProver_top
% 7.26/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_11,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v2_pre_topc(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6387,plain,
% 7.26/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.49      | l1_pre_topc(X1) != iProver_top
% 7.26/1.49      | v2_pre_topc(X1) != iProver_top
% 7.26/1.49      | v2_pre_topc(X0) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7922,plain,
% 7.26/1.49      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.26/1.49      | v2_struct_0(X1) = iProver_top
% 7.26/1.49      | l1_pre_topc(X1) != iProver_top
% 7.26/1.49      | v2_pre_topc(X1) != iProver_top
% 7.26/1.49      | v2_pre_topc(k1_tex_2(X1,X0)) = iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6378,c_6387]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_19273,plain,
% 7.26/1.49      ( v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.26/1.49      | v2_pre_topc(k1_tex_2(sK3,sK0(sK4))) = iProver_top
% 7.26/1.49      | v2_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_12068,c_7922]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_19289,plain,
% 7.26/1.49      ( v2_struct_0(sK3)
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | v2_pre_topc(k1_tex_2(sK3,sK0(sK4)))
% 7.26/1.49      | ~ v2_pre_topc(sK3) ),
% 7.26/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_19273]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_18,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | ~ v7_struct_0(X0)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6479,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,sK3)
% 7.26/1.49      | v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | ~ v7_struct_0(X0)
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | ~ v2_pre_topc(X0) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6815,plain,
% 7.26/1.49      ( ~ m1_pre_topc(k1_tex_2(X0,X1),sK3)
% 7.26/1.49      | v1_tdlat_3(k1_tex_2(X0,X1))
% 7.26/1.49      | v2_struct_0(k1_tex_2(X0,X1))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | ~ v7_struct_0(k1_tex_2(X0,X1))
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | ~ v2_pre_topc(k1_tex_2(X0,X1)) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_6479]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21021,plain,
% 7.26/1.49      ( ~ m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3)
% 7.26/1.49      | v1_tdlat_3(k1_tex_2(sK3,sK0(sK4)))
% 7.26/1.49      | v2_struct_0(k1_tex_2(sK3,sK0(sK4)))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | ~ v7_struct_0(k1_tex_2(sK3,sK0(sK4)))
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | ~ v2_pre_topc(k1_tex_2(sK3,sK0(sK4))) ),
% 7.26/1.49      inference(instantiation,[status(thm)],[c_6815]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21959,plain,
% 7.26/1.49      ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_21657,c_46,c_45,c_43,c_42,c_41,c_1838,c_6792,c_7961,
% 7.26/1.49                 c_8720,c_9851,c_10466,c_12077,c_12079,c_16285,c_19289,
% 7.26/1.49                 c_21021]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_12,plain,
% 7.26/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_14,plain,
% 7.26/1.49      ( ~ v7_struct_0(X0)
% 7.26/1.49      | v1_zfmisc_1(u1_struct_0(X0))
% 7.26/1.49      | ~ l1_struct_0(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_611,plain,
% 7.26/1.49      ( ~ v7_struct_0(X0)
% 7.26/1.49      | v1_zfmisc_1(u1_struct_0(X0))
% 7.26/1.49      | ~ l1_pre_topc(X0) ),
% 7.26/1.49      inference(resolution,[status(thm)],[c_12,c_14]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6366,plain,
% 7.26/1.49      ( v7_struct_0(X0) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 7.26/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21975,plain,
% 7.26/1.49      ( v7_struct_0(sK2(sK3,sK4)) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_21959,c_6366]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21022,plain,
% 7.26/1.49      ( m1_pre_topc(k1_tex_2(sK3,sK0(sK4)),sK3) != iProver_top
% 7.26/1.49      | v1_tdlat_3(k1_tex_2(sK3,sK0(sK4))) = iProver_top
% 7.26/1.49      | v2_struct_0(k1_tex_2(sK3,sK0(sK4))) = iProver_top
% 7.26/1.49      | v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | v7_struct_0(k1_tex_2(sK3,sK0(sK4))) != iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.26/1.49      | v2_pre_topc(k1_tex_2(sK3,sK0(sK4))) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_21021]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_35,plain,
% 7.26/1.49      ( ~ v2_tex_2(X0,X1)
% 7.26/1.49      | m1_pre_topc(sK2(X1,X0),X1)
% 7.26/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v1_xboole_0(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1823,plain,
% 7.26/1.49      ( m1_pre_topc(sK2(X0,X1),X0)
% 7.26/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(X0)
% 7.26/1.49      | ~ v2_pre_topc(X0)
% 7.26/1.49      | v1_xboole_0(X1)
% 7.26/1.49      | sK3 != X0
% 7.26/1.49      | sK4 != X1 ),
% 7.26/1.49      inference(resolution_lifted,[status(thm)],[c_35,c_383]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1824,plain,
% 7.26/1.49      ( m1_pre_topc(sK2(sK3,sK4),sK3)
% 7.26/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | ~ v2_pre_topc(sK3)
% 7.26/1.49      | v1_xboole_0(sK4) ),
% 7.26/1.49      inference(unflattening,[status(thm)],[c_1823]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1826,plain,
% 7.26/1.49      ( v1_zfmisc_1(sK4) | m1_pre_topc(sK2(sK3,sK4),sK3) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_1824,c_46,c_45,c_43,c_42,c_41]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1827,plain,
% 7.26/1.49      ( m1_pre_topc(sK2(sK3,sK4),sK3) | v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_1826]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6355,plain,
% 7.26/1.49      ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_1827]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_21,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.26/1.49      | ~ v1_tdlat_3(X0)
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v2_struct_0(X0)
% 7.26/1.49      | ~ v2_tdlat_3(X1)
% 7.26/1.49      | v7_struct_0(X0)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1) ),
% 7.26/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6380,plain,
% 7.26/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.49      | v1_tdlat_3(X0) != iProver_top
% 7.26/1.49      | v2_struct_0(X1) = iProver_top
% 7.26/1.49      | v2_struct_0(X0) = iProver_top
% 7.26/1.49      | v2_tdlat_3(X1) != iProver_top
% 7.26/1.49      | v7_struct_0(X0) = iProver_top
% 7.26/1.49      | l1_pre_topc(X1) != iProver_top
% 7.26/1.49      | v2_pre_topc(X1) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_8501,plain,
% 7.26/1.49      ( v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.26/1.49      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.26/1.49      | v2_struct_0(sK3) = iProver_top
% 7.26/1.49      | v2_tdlat_3(sK3) != iProver_top
% 7.26/1.49      | v7_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.26/1.49      | v2_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6355,c_6380]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_13,plain,
% 7.26/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_6386,plain,
% 7.26/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.26/1.49      | l1_pre_topc(X1) != iProver_top
% 7.26/1.49      | l1_pre_topc(X0) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7035,plain,
% 7.26/1.49      ( v1_zfmisc_1(sK4) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
% 7.26/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_6355,c_6386]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_36,plain,
% 7.26/1.49      ( ~ v2_tex_2(X0,X1)
% 7.26/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | v1_tdlat_3(sK2(X1,X0))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v1_xboole_0(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1809,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | v1_tdlat_3(sK2(X1,X0))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v1_xboole_0(X0)
% 7.26/1.49      | sK3 != X1
% 7.26/1.49      | sK4 != X0 ),
% 7.26/1.49      inference(resolution_lifted,[status(thm)],[c_36,c_383]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1810,plain,
% 7.26/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.26/1.49      | v1_tdlat_3(sK2(sK3,sK4))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | ~ v2_pre_topc(sK3)
% 7.26/1.49      | v1_xboole_0(sK4) ),
% 7.26/1.49      inference(unflattening,[status(thm)],[c_1809]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1812,plain,
% 7.26/1.49      ( v1_zfmisc_1(sK4) | v1_tdlat_3(sK2(sK3,sK4)) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_1810,c_46,c_45,c_43,c_42,c_41]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1813,plain,
% 7.26/1.49      ( v1_tdlat_3(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_1812]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1814,plain,
% 7.26/1.49      ( v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_38,plain,
% 7.26/1.49      ( ~ v2_tex_2(X0,X1)
% 7.26/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ v2_struct_0(sK2(X1,X0))
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v1_xboole_0(X0) ),
% 7.26/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1781,plain,
% 7.26/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.26/1.49      | v2_struct_0(X1)
% 7.26/1.49      | ~ v2_struct_0(sK2(X1,X0))
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(X1)
% 7.26/1.49      | ~ v2_pre_topc(X1)
% 7.26/1.49      | v1_xboole_0(X0)
% 7.26/1.49      | sK3 != X1
% 7.26/1.49      | sK4 != X0 ),
% 7.26/1.49      inference(resolution_lifted,[status(thm)],[c_38,c_383]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1782,plain,
% 7.26/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.26/1.49      | ~ v2_struct_0(sK2(sK3,sK4))
% 7.26/1.49      | v2_struct_0(sK3)
% 7.26/1.49      | v1_zfmisc_1(sK4)
% 7.26/1.49      | ~ l1_pre_topc(sK3)
% 7.26/1.49      | ~ v2_pre_topc(sK3)
% 7.26/1.49      | v1_xboole_0(sK4) ),
% 7.26/1.49      inference(unflattening,[status(thm)],[c_1781]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1784,plain,
% 7.26/1.49      ( v1_zfmisc_1(sK4) | ~ v2_struct_0(sK2(sK3,sK4)) ),
% 7.26/1.49      inference(global_propositional_subsumption,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_1782,c_46,c_45,c_43,c_42,c_41]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1785,plain,
% 7.26/1.49      ( ~ v2_struct_0(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 7.26/1.49      inference(renaming,[status(thm)],[c_1784]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_1786,plain,
% 7.26/1.49      ( v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 7.26/1.49      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_44,negated_conjecture,
% 7.26/1.49      ( v2_tdlat_3(sK3) ),
% 7.26/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_49,plain,
% 7.26/1.49      ( v2_tdlat_3(sK3) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_48,plain,
% 7.26/1.49      ( v2_pre_topc(sK3) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(contradiction,plain,
% 7.26/1.49      ( $false ),
% 7.26/1.49      inference(minisat,
% 7.26/1.49                [status(thm)],
% 7.26/1.49                [c_21975,c_21022,c_19273,c_16283,c_12074,c_12072,c_10467,
% 7.26/1.49                 c_9852,c_8721,c_8501,c_7962,c_7035,c_6791,c_1814,c_1786,
% 7.26/1.49                 c_51,c_50,c_49,c_48,c_47]) ).
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.49  
% 7.26/1.49  ------                               Statistics
% 7.26/1.49  
% 7.26/1.49  ------ General
% 7.26/1.49  
% 7.26/1.49  abstr_ref_over_cycles:                  0
% 7.26/1.49  abstr_ref_under_cycles:                 0
% 7.26/1.49  gc_basic_clause_elim:                   0
% 7.26/1.49  forced_gc_time:                         0
% 7.26/1.49  parsing_time:                           0.01
% 7.26/1.49  unif_index_cands_time:                  0.
% 7.26/1.49  unif_index_add_time:                    0.
% 7.26/1.49  orderings_time:                         0.
% 7.26/1.49  out_proof_time:                         0.016
% 7.26/1.49  total_time:                             0.545
% 7.26/1.49  num_of_symbols:                         56
% 7.26/1.49  num_of_terms:                           15285
% 7.26/1.49  
% 7.26/1.49  ------ Preprocessing
% 7.26/1.49  
% 7.26/1.49  num_of_splits:                          0
% 7.26/1.49  num_of_split_atoms:                     0
% 7.26/1.49  num_of_reused_defs:                     0
% 7.26/1.49  num_eq_ax_congr_red:                    34
% 7.26/1.49  num_of_sem_filtered_clauses:            1
% 7.26/1.49  num_of_subtypes:                        0
% 7.26/1.49  monotx_restored_types:                  0
% 7.26/1.49  sat_num_of_epr_types:                   0
% 7.26/1.49  sat_num_of_non_cyclic_types:            0
% 7.26/1.49  sat_guarded_non_collapsed_types:        0
% 7.26/1.49  num_pure_diseq_elim:                    0
% 7.26/1.49  simp_replaced_by:                       0
% 7.26/1.49  res_preprocessed:                       217
% 7.26/1.49  prep_upred:                             0
% 7.26/1.49  prep_unflattend:                        164
% 7.26/1.49  smt_new_axioms:                         0
% 7.26/1.49  pred_elim_cands:                        13
% 7.26/1.49  pred_elim:                              2
% 7.26/1.49  pred_elim_cl:                           -2
% 7.26/1.49  pred_elim_cycles:                       17
% 7.26/1.49  merged_defs:                            18
% 7.26/1.49  merged_defs_ncl:                        0
% 7.26/1.49  bin_hyper_res:                          18
% 7.26/1.49  prep_cycles:                            4
% 7.26/1.49  pred_elim_time:                         0.07
% 7.26/1.49  splitting_time:                         0.
% 7.26/1.49  sem_filter_time:                        0.
% 7.26/1.49  monotx_time:                            0.
% 7.26/1.49  subtype_inf_time:                       0.
% 7.26/1.49  
% 7.26/1.49  ------ Problem properties
% 7.26/1.49  
% 7.26/1.49  clauses:                                45
% 7.26/1.49  conjectures:                            6
% 7.26/1.49  epr:                                    15
% 7.26/1.49  horn:                                   23
% 7.26/1.49  ground:                                 11
% 7.26/1.49  unary:                                  7
% 7.26/1.49  binary:                                 14
% 7.26/1.49  lits:                                   162
% 7.26/1.49  lits_eq:                                9
% 7.26/1.49  fd_pure:                                0
% 7.26/1.49  fd_pseudo:                              0
% 7.26/1.49  fd_cond:                                0
% 7.26/1.49  fd_pseudo_cond:                         2
% 7.26/1.49  ac_symbols:                             0
% 7.26/1.49  
% 7.26/1.49  ------ Propositional Solver
% 7.26/1.49  
% 7.26/1.49  prop_solver_calls:                      35
% 7.26/1.49  prop_fast_solver_calls:                 3509
% 7.26/1.49  smt_solver_calls:                       0
% 7.26/1.49  smt_fast_solver_calls:                  0
% 7.26/1.49  prop_num_of_clauses:                    7095
% 7.26/1.49  prop_preprocess_simplified:             16191
% 7.26/1.49  prop_fo_subsumed:                       163
% 7.26/1.49  prop_solver_time:                       0.
% 7.26/1.49  smt_solver_time:                        0.
% 7.26/1.49  smt_fast_solver_time:                   0.
% 7.26/1.49  prop_fast_solver_time:                  0.
% 7.26/1.49  prop_unsat_core_time:                   0.
% 7.26/1.49  
% 7.26/1.49  ------ QBF
% 7.26/1.49  
% 7.26/1.49  qbf_q_res:                              0
% 7.26/1.49  qbf_num_tautologies:                    0
% 7.26/1.49  qbf_prep_cycles:                        0
% 7.26/1.49  
% 7.26/1.49  ------ BMC1
% 7.26/1.49  
% 7.26/1.49  bmc1_current_bound:                     -1
% 7.26/1.49  bmc1_last_solved_bound:                 -1
% 7.26/1.49  bmc1_unsat_core_size:                   -1
% 7.26/1.49  bmc1_unsat_core_parents_size:           -1
% 7.26/1.49  bmc1_merge_next_fun:                    0
% 7.26/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.26/1.49  
% 7.26/1.49  ------ Instantiation
% 7.26/1.49  
% 7.26/1.49  inst_num_of_clauses:                    1595
% 7.26/1.49  inst_num_in_passive:                    729
% 7.26/1.49  inst_num_in_active:                     765
% 7.26/1.49  inst_num_in_unprocessed:                101
% 7.26/1.49  inst_num_of_loops:                      1150
% 7.26/1.49  inst_num_of_learning_restarts:          0
% 7.26/1.49  inst_num_moves_active_passive:          377
% 7.26/1.49  inst_lit_activity:                      0
% 7.26/1.49  inst_lit_activity_moves:                0
% 7.26/1.49  inst_num_tautologies:                   0
% 7.26/1.49  inst_num_prop_implied:                  0
% 7.26/1.49  inst_num_existing_simplified:           0
% 7.26/1.49  inst_num_eq_res_simplified:             0
% 7.26/1.49  inst_num_child_elim:                    0
% 7.26/1.49  inst_num_of_dismatching_blockings:      1923
% 7.26/1.49  inst_num_of_non_proper_insts:           2544
% 7.26/1.49  inst_num_of_duplicates:                 0
% 7.26/1.49  inst_inst_num_from_inst_to_res:         0
% 7.26/1.49  inst_dismatching_checking_time:         0.
% 7.26/1.49  
% 7.26/1.49  ------ Resolution
% 7.26/1.49  
% 7.26/1.49  res_num_of_clauses:                     0
% 7.26/1.49  res_num_in_passive:                     0
% 7.26/1.49  res_num_in_active:                      0
% 7.26/1.49  res_num_of_loops:                       221
% 7.26/1.49  res_forward_subset_subsumed:            51
% 7.26/1.49  res_backward_subset_subsumed:           2
% 7.26/1.49  res_forward_subsumed:                   0
% 7.26/1.49  res_backward_subsumed:                  0
% 7.26/1.49  res_forward_subsumption_resolution:     9
% 7.26/1.49  res_backward_subsumption_resolution:    0
% 7.26/1.49  res_clause_to_clause_subsumption:       2167
% 7.26/1.49  res_orphan_elimination:                 0
% 7.26/1.49  res_tautology_del:                      405
% 7.26/1.49  res_num_eq_res_simplified:              0
% 7.26/1.49  res_num_sel_changes:                    0
% 7.26/1.49  res_moves_from_active_to_pass:          0
% 7.26/1.49  
% 7.26/1.49  ------ Superposition
% 7.26/1.49  
% 7.26/1.49  sup_time_total:                         0.
% 7.26/1.49  sup_time_generating:                    0.
% 7.26/1.49  sup_time_sim_full:                      0.
% 7.26/1.49  sup_time_sim_immed:                     0.
% 7.26/1.49  
% 7.26/1.49  sup_num_of_clauses:                     659
% 7.26/1.49  sup_num_in_active:                      212
% 7.26/1.49  sup_num_in_passive:                     447
% 7.26/1.49  sup_num_of_loops:                       228
% 7.26/1.49  sup_fw_superposition:                   403
% 7.26/1.49  sup_bw_superposition:                   509
% 7.26/1.49  sup_immediate_simplified:               165
% 7.26/1.49  sup_given_eliminated:                   0
% 7.26/1.49  comparisons_done:                       0
% 7.26/1.49  comparisons_avoided:                    42
% 7.26/1.49  
% 7.26/1.49  ------ Simplifications
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  sim_fw_subset_subsumed:                 51
% 7.26/1.49  sim_bw_subset_subsumed:                 14
% 7.26/1.49  sim_fw_subsumed:                        38
% 7.26/1.49  sim_bw_subsumed:                        8
% 7.26/1.49  sim_fw_subsumption_res:                 0
% 7.26/1.49  sim_bw_subsumption_res:                 0
% 7.26/1.49  sim_tautology_del:                      28
% 7.26/1.49  sim_eq_tautology_del:                   21
% 7.26/1.49  sim_eq_res_simp:                        0
% 7.26/1.49  sim_fw_demodulated:                     33
% 7.26/1.49  sim_bw_demodulated:                     11
% 7.26/1.49  sim_light_normalised:                   38
% 7.26/1.49  sim_joinable_taut:                      0
% 7.26/1.49  sim_joinable_simp:                      0
% 7.26/1.49  sim_ac_normalised:                      0
% 7.26/1.49  sim_smt_subsumption:                    0
% 7.26/1.49  
%------------------------------------------------------------------------------
