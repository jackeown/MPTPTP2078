%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:44 EST 2020

% Result     : Theorem 43.43s
% Output     : CNFRefutation 43.43s
% Verified   : 
% Statistics : Number of formulae       :  303 (9813 expanded)
%              Number of clauses        :  195 (2378 expanded)
%              Number of leaves         :   33 (3083 expanded)
%              Depth                    :   30
%              Number of atoms          : 1192 (72887 expanded)
%              Number of equality atoms :  398 (10544 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK10(X2)) = k6_domain_1(u1_struct_0(X0),X2)
        & v3_pre_topc(sK10(X2),X0)
        & m1_subset_1(sK10(X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK9,X0)
        & ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),sK9,X3) = k6_domain_1(u1_struct_0(X0),X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,sK9)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK8)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(sK8),X1,X3) = k6_domain_1(u1_struct_0(sK8),X2)
                  & v3_pre_topc(X3,sK8)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK8)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ~ v2_tex_2(sK9,sK8)
    & ! [X2] :
        ( ( k9_subset_1(u1_struct_0(sK8),sK9,sK10(X2)) = k6_domain_1(u1_struct_0(sK8),X2)
          & v3_pre_topc(sK10(X2),sK8)
          & m1_subset_1(sK10(X2),k1_zfmisc_1(u1_struct_0(sK8))) )
        | ~ r2_hidden(X2,sK9)
        | ~ m1_subset_1(X2,u1_struct_0(sK8)) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f51,f72,f71,f70])).

fof(f114,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f73])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f116,plain,(
    ! [X2] :
      ( m1_subset_1(sK10(X2),k1_zfmisc_1(u1_struct_0(sK8)))
      | ~ r2_hidden(X2,sK9)
      | ~ m1_subset_1(X2,u1_struct_0(sK8)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f115,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f73])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK5(X0,X1)) = X1
        & m1_pre_topc(sK5(X0,X1),X0)
        & ~ v2_struct_0(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK5(X0,X1)) = X1
            & m1_pre_topc(sK5(X0,X1),X0)
            & ~ v2_struct_0(sK5(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f64])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK5(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f112,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f73])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,(
    ~ v2_tex_2(sK9,sK8) ),
    inference(cnf_transformation,[],[f73])).

fof(f113,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f73])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f96,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_tarski(X2) = X1
                 => v3_pre_topc(X1,X0) ) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X1,X0)
          & k1_tarski(X2) = X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ v3_pre_topc(X1,X0)
        & k1_tarski(sK7(X0)) = X1
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_pre_topc(sK6(X0),X0)
            & k1_tarski(X2) = sK6(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ( ~ v3_pre_topc(sK6(X0),X0)
        & k1_tarski(sK7(X0)) = sK6(X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f67,f66])).

fof(f105,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | k1_tarski(sK7(X0)) = sK6(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK5(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK5(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f16,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f108])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f118,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK8),sK9,sK10(X2)) = k6_domain_1(u1_struct_0(sK8),X2)
      | ~ r2_hidden(X2,sK9)
      | ~ m1_subset_1(X2,u1_struct_0(sK8)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f57])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f62,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f59,f62,f61,f60])).

fof(f86,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f120,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f28,f53,f52])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f117,plain,(
    ! [X2] :
      ( v3_pre_topc(sK10(X2),sK8)
      | ~ r2_hidden(X2,sK9)
      | ~ m1_subset_1(X2,u1_struct_0(sK8)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f106,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v3_pre_topc(sK6(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3289,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_21,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_533,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_21,c_3])).

cnf(c_3284,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_4028,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_3289,c_3284])).

cnf(c_41,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3291,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4037,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10(X0),k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4028,c_3291])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3290,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_4038,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4028,c_3290])).

cnf(c_37,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3293,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4368,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4038,c_3293])).

cnf(c_4472,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(sK10(X0),k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4037,c_4368])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK5(X1,X0),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3299,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_pre_topc(sK5(X1,X0),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5540,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | m1_pre_topc(sK5(sK8,X0),sK8) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_3299])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_46,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_48,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6789,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | m1_pre_topc(sK5(sK8,X0),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5540,c_46,c_48])).

cnf(c_6790,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | m1_pre_topc(sK5(sK8,X0),sK8) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6789])).

cnf(c_6797,plain,
    ( m1_pre_topc(sK5(sK8,sK9),sK8) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4038,c_6790])).

cnf(c_49,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_36,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_38,negated_conjecture,
    ( ~ v2_tex_2(sK9,sK8) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_844,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_38])).

cnf(c_845,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(sK8)
    | ~ v1_xboole_0(sK9)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_847,plain,
    ( ~ v1_xboole_0(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_45,c_44,c_43,c_42])).

cnf(c_1524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK5(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_847])).

cnf(c_1525,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_pre_topc(sK5(X0,sK9),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1524])).

cnf(c_1526,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(sK5(X0,sK9),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_1528,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_pre_topc(sK5(sK8,sK9),sK8) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1526])).

cnf(c_6937,plain,
    ( m1_pre_topc(sK5(sK8,sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6797,c_46,c_48,c_49,c_1528])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3303,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6944,plain,
    ( l1_pre_topc(sK5(sK8,sK9)) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6937,c_3303])).

cnf(c_3780,plain,
    ( ~ m1_pre_topc(sK5(sK8,sK9),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK5(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3781,plain,
    ( m1_pre_topc(sK5(sK8,sK9),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3780])).

cnf(c_3783,plain,
    ( m1_pre_topc(sK5(sK8,sK9),sK8) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3781])).

cnf(c_7101,plain,
    ( l1_pre_topc(sK5(sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6944,c_46,c_48,c_49,c_1528,c_3783])).

cnf(c_30,plain,
    ( v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k1_tarski(sK7(X0)) = sK6(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3297,plain,
    ( k1_tarski(sK7(X0)) = sK6(X0)
    | v1_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7105,plain,
    ( k1_tarski(sK7(sK5(sK8,sK9))) = sK6(sK5(sK8,sK9))
    | v1_tdlat_3(sK5(sK8,sK9)) = iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7101,c_3297])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK5(X1,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1506,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK5(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_847])).

cnf(c_1507,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK5(X0,sK9))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1506])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v2_struct_0(sK5(sK8,sK9))
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_1527,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_pre_topc(sK5(sK8,sK9),sK8)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK5(X1,X0)) = X0
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_847])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK5(X0,sK9)) = sK9 ),
    inference(unflattening,[status(thm)],[c_1542])).

cnf(c_1545,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8)
    | u1_struct_0(sK5(sK8,sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_33,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_817,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK9
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_38])).

cnf(c_818,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_pre_topc(X0,sK8)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8)
    | u1_struct_0(X0) != sK9 ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_822,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_pre_topc(X0,sK8)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_818,c_45,c_43])).

cnf(c_3517,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_pre_topc(sK5(sK8,sK9),sK8)
    | ~ v1_tdlat_3(sK5(sK8,sK9))
    | v2_struct_0(sK5(sK8,sK9))
    | u1_struct_0(sK5(sK8,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_3645,plain,
    ( v1_tdlat_3(sK5(sK8,sK9))
    | ~ l1_pre_topc(sK5(sK8,sK9))
    | ~ v2_pre_topc(sK5(sK8,sK9))
    | k1_tarski(sK7(sK5(sK8,sK9))) = sK6(sK5(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3782,plain,
    ( ~ m1_pre_topc(sK5(sK8,sK9),sK8)
    | l1_pre_topc(sK5(sK8,sK9))
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_3780])).

cnf(c_2671,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3871,plain,
    ( k1_zfmisc_1(u1_struct_0(sK8)) = k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_2678,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3622,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_2678])).

cnf(c_3992,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | X0 != sK9
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3622])).

cnf(c_4094,plain,
    ( m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | u1_struct_0(sK5(sK8,sK9)) != sK9
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3992])).

cnf(c_4096,plain,
    ( m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | u1_struct_0(sK5(sK8,sK9)) != sK9
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4094])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4516,plain,
    ( ~ m1_pre_topc(sK5(sK8,sK9),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK5(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4518,plain,
    ( ~ m1_pre_topc(sK5(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | v2_pre_topc(sK5(sK8,sK9))
    | ~ v2_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_4516])).

cnf(c_69833,plain,
    ( k1_tarski(sK7(sK5(sK8,sK9))) = sK6(sK5(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7105,c_45,c_44,c_43,c_42,c_1509,c_1527,c_1545,c_3517,c_3645,c_3782,c_3871,c_4096,c_4518])).

cnf(c_3300,plain,
    ( u1_struct_0(sK5(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5494,plain,
    ( u1_struct_0(sK5(sK8,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_3300])).

cnf(c_5697,plain,
    ( v1_xboole_0(X0) = iProver_top
    | u1_struct_0(sK5(sK8,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5494,c_46,c_48])).

cnf(c_5698,plain,
    ( u1_struct_0(sK5(sK8,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5697])).

cnf(c_5705,plain,
    ( u1_struct_0(sK5(sK8,sK9)) = sK9
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4038,c_5698])).

cnf(c_5716,plain,
    ( u1_struct_0(sK5(sK8,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5705,c_45,c_43,c_42,c_1545])).

cnf(c_31,plain,
    ( m1_subset_1(sK7(X0),u1_struct_0(X0))
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3296,plain,
    ( m1_subset_1(sK7(X0),u1_struct_0(X0)) = iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5723,plain,
    ( m1_subset_1(sK7(sK5(sK8,sK9)),sK9) = iProver_top
    | v1_tdlat_3(sK5(sK8,sK9)) = iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5716,c_3296])).

cnf(c_47,plain,
    ( v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_1508,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5(X0,sK9)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1507])).

cnf(c_1510,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v2_struct_0(sK5(sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_3518,plain,
    ( u1_struct_0(sK5(sK8,sK9)) != sK9
    | m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_pre_topc(sK5(sK8,sK9),sK8) != iProver_top
    | v1_tdlat_3(sK5(sK8,sK9)) != iProver_top
    | v2_struct_0(sK5(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3517])).

cnf(c_4095,plain,
    ( u1_struct_0(sK5(sK8,sK9)) != sK9
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK8))
    | m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4094])).

cnf(c_4097,plain,
    ( u1_struct_0(sK5(sK8,sK9)) != sK9
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8))
    | m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4095])).

cnf(c_4517,plain,
    ( m1_pre_topc(sK5(sK8,sK9),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4516])).

cnf(c_4519,plain,
    ( m1_pre_topc(sK5(sK8,sK9),sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) = iProver_top
    | v2_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4517])).

cnf(c_22481,plain,
    ( m1_subset_1(sK7(sK5(sK8,sK9)),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5723,c_45,c_46,c_47,c_43,c_48,c_42,c_49,c_1510,c_1528,c_1545,c_3518,c_3783,c_3871,c_4097,c_4519])).

cnf(c_35,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3294,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_22485,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_22481,c_3294])).

cnf(c_846,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v1_xboole_0(sK9) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_4761,plain,
    ( r2_hidden(sK7(X0),u1_struct_0(X0)) = iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3296,c_3294])).

cnf(c_14780,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),sK9) = iProver_top
    | v1_tdlat_3(sK5(sK8,sK9)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5(sK8,sK9))) = iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5716,c_4761])).

cnf(c_14781,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),sK9) = iProver_top
    | v1_tdlat_3(sK5(sK8,sK9)) = iProver_top
    | v1_xboole_0(sK9) = iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14780,c_5716])).

cnf(c_22665,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22485,c_45,c_46,c_47,c_43,c_48,c_42,c_49,c_846,c_1510,c_1528,c_1545,c_3518,c_3783,c_3871,c_4097,c_4519,c_14781])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3302,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4554,plain,
    ( k6_domain_1(k2_struct_0(sK8),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK9) != iProver_top
    | v1_xboole_0(k2_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4368,c_3302])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_102,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_104,plain,
    ( v2_struct_0(sK8) = iProver_top
    | v1_xboole_0(u1_struct_0(sK8)) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_107,plain,
    ( l1_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_106,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_108,plain,
    ( l1_struct_0(sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_161,plain,
    ( ~ l1_struct_0(sK8)
    | u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2682,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3401,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK8))
    | u1_struct_0(sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_2682])).

cnf(c_3520,plain,
    ( v1_xboole_0(u1_struct_0(sK8))
    | ~ v1_xboole_0(k2_struct_0(sK8))
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3401])).

cnf(c_3524,plain,
    ( u1_struct_0(sK8) != k2_struct_0(sK8)
    | v1_xboole_0(u1_struct_0(sK8)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3520])).

cnf(c_13293,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | k6_domain_1(k2_struct_0(sK8),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4554,c_46,c_43,c_48,c_104,c_107,c_108,c_161,c_3524])).

cnf(c_13294,plain,
    ( k6_domain_1(k2_struct_0(sK8),X0) = k1_tarski(X0)
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_13293])).

cnf(c_22670,plain,
    ( k6_domain_1(k2_struct_0(sK8),sK7(sK5(sK8,sK9))) = k1_tarski(sK7(sK5(sK8,sK9))) ),
    inference(superposition,[status(thm)],[c_22665,c_13294])).

cnf(c_39,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k9_subset_1(u1_struct_0(sK8),sK9,sK10(X0)) = k6_domain_1(u1_struct_0(sK8),X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3292,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,sK10(X0)) = k6_domain_1(u1_struct_0(sK8),X0)
    | r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4036,plain,
    ( k9_subset_1(k2_struct_0(sK8),sK9,sK10(X0)) = k6_domain_1(k2_struct_0(sK8),X0)
    | r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4028,c_3292])).

cnf(c_4497,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | k9_subset_1(k2_struct_0(sK8),sK9,sK10(X0)) = k6_domain_1(k2_struct_0(sK8),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4036,c_4368])).

cnf(c_4498,plain,
    ( k9_subset_1(k2_struct_0(sK8),sK9,sK10(X0)) = k6_domain_1(k2_struct_0(sK8),X0)
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_4497])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3309,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4209,plain,
    ( k9_subset_1(k2_struct_0(sK8),sK9,X0) = k9_subset_1(k2_struct_0(sK8),X0,sK9) ),
    inference(superposition,[status(thm)],[c_4038,c_3309])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3301,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3759,plain,
    ( k9_subset_1(u1_struct_0(sK8),X0,sK9) = k3_xboole_0(X0,sK9) ),
    inference(superposition,[status(thm)],[c_3290,c_3301])).

cnf(c_4033,plain,
    ( k9_subset_1(k2_struct_0(sK8),X0,sK9) = k3_xboole_0(X0,sK9) ),
    inference(demodulation,[status(thm)],[c_4028,c_3759])).

cnf(c_4210,plain,
    ( k9_subset_1(k2_struct_0(sK8),sK9,X0) = k3_xboole_0(X0,sK9) ),
    inference(light_normalisation,[status(thm)],[c_4209,c_4033])).

cnf(c_4503,plain,
    ( k6_domain_1(k2_struct_0(sK8),X0) = k3_xboole_0(sK10(X0),sK9)
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4498,c_4210])).

cnf(c_22676,plain,
    ( k6_domain_1(k2_struct_0(sK8),sK7(sK5(sK8,sK9))) = k3_xboole_0(sK10(sK7(sK5(sK8,sK9))),sK9) ),
    inference(superposition,[status(thm)],[c_22665,c_4503])).

cnf(c_22685,plain,
    ( k3_xboole_0(sK10(sK7(sK5(sK8,sK9))),sK9) = k1_tarski(sK7(sK5(sK8,sK9))) ),
    inference(demodulation,[status(thm)],[c_22670,c_22676])).

cnf(c_7106,plain,
    ( u1_struct_0(sK5(sK8,sK9)) = k2_struct_0(sK5(sK8,sK9)) ),
    inference(superposition,[status(thm)],[c_7101,c_3284])).

cnf(c_7107,plain,
    ( k2_struct_0(sK5(sK8,sK9)) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_7106,c_5716])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3308,plain,
    ( sP0(X0,X1) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7195,plain,
    ( sP0(sK5(sK8,sK9),X0) != iProver_top
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5(sK8,sK9)),X1,k2_struct_0(sK5(sK8,sK9))),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK5(sK8,sK9)),X1,sK9),k1_zfmisc_1(u1_struct_0(sK5(sK8,sK9)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7107,c_3308])).

cnf(c_7196,plain,
    ( sP0(sK5(sK8,sK9),X0) != iProver_top
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | r2_hidden(k9_subset_1(sK9,X1,sK9),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k9_subset_1(sK9,X1,sK9),k1_zfmisc_1(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7195,c_5716,c_7107])).

cnf(c_19,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_522,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_21,c_19])).

cnf(c_3285,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_6171,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) = k3_xboole_0(X1,k2_struct_0(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3285,c_3301])).

cnf(c_7416,plain,
    ( k9_subset_1(u1_struct_0(sK5(sK8,sK9)),X0,k2_struct_0(sK5(sK8,sK9))) = k3_xboole_0(X0,k2_struct_0(sK5(sK8,sK9))) ),
    inference(superposition,[status(thm)],[c_7101,c_6171])).

cnf(c_7417,plain,
    ( k9_subset_1(sK9,X0,sK9) = k3_xboole_0(X0,sK9) ),
    inference(light_normalisation,[status(thm)],[c_7416,c_5716,c_7107])).

cnf(c_12477,plain,
    ( sP0(sK5(sK8,sK9),X0) != iProver_top
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | r2_hidden(k3_xboole_0(X1,sK9),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k3_xboole_0(X1,sK9),k1_zfmisc_1(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7196,c_7417])).

cnf(c_12485,plain,
    ( sP0(sK5(sK8,sK9),sK8) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK8)) != iProver_top
    | r2_hidden(k3_xboole_0(X0,sK9),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,sK9),k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_12477])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_554,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_18,c_7])).

cnf(c_558,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_22])).

cnf(c_559,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_558])).

cnf(c_3482,plain,
    ( sP0(X0,sK8)
    | ~ m1_pre_topc(X0,sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_3602,plain,
    ( sP0(sK5(sK8,sK9),sK8)
    | ~ m1_pre_topc(sK5(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_3482])).

cnf(c_3603,plain,
    ( sP0(sK5(sK8,sK9),sK8) = iProver_top
    | m1_pre_topc(sK5(sK8,sK9),sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3602])).

cnf(c_7194,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK5(sK8,sK9)))) = iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7107,c_3285])).

cnf(c_7197,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(sK9)) = iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7194,c_5716])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7526,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK9),k1_zfmisc_1(sK9)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7417,c_3304])).

cnf(c_12635,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | r2_hidden(k3_xboole_0(X0,sK9),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12485,c_46,c_48,c_49,c_1528,c_3603,c_3783,c_7197,c_7526])).

cnf(c_12636,plain,
    ( r2_hidden(X0,u1_pre_topc(sK8)) != iProver_top
    | r2_hidden(k3_xboole_0(X0,sK9),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12635])).

cnf(c_33709,plain,
    ( r2_hidden(sK10(sK7(sK5(sK8,sK9))),u1_pre_topc(sK8)) != iProver_top
    | r2_hidden(k1_tarski(sK7(sK5(sK8,sK9))),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(sK10(sK7(sK5(sK8,sK9))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22685,c_12636])).

cnf(c_3648,plain,
    ( m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9)))
    | v1_tdlat_3(sK5(sK8,sK9))
    | ~ l1_pre_topc(sK5(sK8,sK9))
    | ~ v2_pre_topc(sK5(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3649,plain,
    ( m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9))) = iProver_top
    | v1_tdlat_3(sK5(sK8,sK9)) = iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3648])).

cnf(c_508,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_21,c_23])).

cnf(c_5387,plain,
    ( v2_struct_0(sK5(sK8,sK9))
    | ~ v1_xboole_0(u1_struct_0(sK5(sK8,sK9)))
    | ~ l1_pre_topc(sK5(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_5388,plain,
    ( v2_struct_0(sK5(sK8,sK9)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5(sK8,sK9))) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5387])).

cnf(c_6331,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9)))
    | ~ m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9)))
    | v1_xboole_0(u1_struct_0(sK5(sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_6332,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5(sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6331])).

cnf(c_8391,plain,
    ( ~ r2_hidden(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9)))
    | m1_subset_1(sK7(sK5(sK8,sK9)),X0)
    | ~ m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_19477,plain,
    ( ~ r2_hidden(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9)))
    | m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_8391])).

cnf(c_19481,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9))) != iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19477])).

cnf(c_19483,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),u1_struct_0(sK5(sK8,sK9))) != iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(u1_struct_0(sK5(sK8,sK9)),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19481])).

cnf(c_5,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | v3_pre_topc(sK10(X0),sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_628,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,sK9)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK10(X2) != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_40])).

cnf(c_629,plain,
    ( ~ r2_hidden(X0,sK9)
    | r2_hidden(sK10(X0),u1_pre_topc(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_633,plain,
    ( ~ r2_hidden(X0,sK9)
    | r2_hidden(sK10(X0),u1_pre_topc(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_43,c_41])).

cnf(c_31333,plain,
    ( r2_hidden(sK10(sK7(sK5(sK8,sK9))),u1_pre_topc(sK8))
    | ~ r2_hidden(sK7(sK5(sK8,sK9)),sK9)
    | ~ m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_31340,plain,
    ( r2_hidden(sK10(sK7(sK5(sK8,sK9))),u1_pre_topc(sK8)) = iProver_top
    | r2_hidden(sK7(sK5(sK8,sK9)),sK9) != iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9)),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31333])).

cnf(c_33844,plain,
    ( r2_hidden(k1_tarski(sK7(sK5(sK8,sK9))),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(sK10(sK7(sK5(sK8,sK9))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33709,c_45,c_46,c_47,c_43,c_48,c_42,c_49,c_846,c_1510,c_1528,c_1545,c_3518,c_3649,c_3783,c_3871,c_4097,c_4519,c_5388,c_6332,c_14781,c_19483,c_31340])).

cnf(c_69839,plain,
    ( r2_hidden(sK6(sK5(sK8,sK9)),u1_pre_topc(sK5(sK8,sK9))) = iProver_top
    | m1_subset_1(sK10(sK7(sK5(sK8,sK9))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_69833,c_33844])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,plain,
    ( ~ v3_pre_topc(sK6(X0),X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_604,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | X2 != X1
    | sK6(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_29])).

cnf(c_605,plain,
    ( ~ r2_hidden(sK6(X0),u1_pre_topc(X0))
    | ~ m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_32,plain,
    ( m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_609,plain,
    ( ~ r2_hidden(sK6(X0),u1_pre_topc(X0))
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_32])).

cnf(c_3647,plain,
    ( ~ r2_hidden(sK6(sK5(sK8,sK9)),u1_pre_topc(sK5(sK8,sK9)))
    | v1_tdlat_3(sK5(sK8,sK9))
    | ~ l1_pre_topc(sK5(sK8,sK9))
    | ~ v2_pre_topc(sK5(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_3651,plain,
    ( r2_hidden(sK6(sK5(sK8,sK9)),u1_pre_topc(sK5(sK8,sK9))) != iProver_top
    | v1_tdlat_3(sK5(sK8,sK9)) = iProver_top
    | l1_pre_topc(sK5(sK8,sK9)) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3647])).

cnf(c_149045,plain,
    ( m1_subset_1(sK10(sK7(sK5(sK8,sK9))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_69839,c_45,c_46,c_47,c_43,c_48,c_42,c_49,c_1510,c_1528,c_1545,c_3518,c_3651,c_3783,c_3871,c_4097,c_4519])).

cnf(c_149049,plain,
    ( r2_hidden(sK7(sK5(sK8,sK9)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4472,c_149045])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_149049,c_14781,c_4519,c_4097,c_3871,c_3783,c_3518,c_1545,c_1528,c_1510,c_846,c_49,c_42,c_48,c_43,c_47,c_46,c_45])).


%------------------------------------------------------------------------------
