%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:32 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 310 expanded)
%              Number of clauses        :   74 (  95 expanded)
%              Number of leaves         :   15 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  476 (1851 expanded)
%              Number of equality atoms :  102 ( 308 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)))
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))
              & ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
    & ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f30,f29,f28])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_669,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_1032,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X0_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X0_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1146,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(X0_47,X0_46)
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(X0_47,X0_46)
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_4327,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_1145,plain,
    ( X0_46 != X1_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X1_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1301,plain,
    ( X0_46 != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = X0_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_3505,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_1307,plain,
    ( X0_46 != X1_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X1_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1653,plain,
    ( X0_46 != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = X0_46
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_3490,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_662,plain,
    ( m1_subset_1(X0_46,X1_46)
    | ~ m1_subset_1(X2_46,k1_zfmisc_1(X1_46))
    | ~ r2_hidden(X0_46,X2_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1080,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(X0_46))
    | m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),X0_46)
    | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_2237,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),u1_struct_0(sK1))
    | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_1874,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_46)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_1876,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | m1_subset_1(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_1053,plain,
    ( m1_subset_1(X0_46,X1_46)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X2_46)),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_46 != u1_struct_0(k1_tex_2(sK1,X2_46))
    | X1_46 != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_1278,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X1_46)),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_46 != u1_struct_0(k1_tex_2(sK1,X1_46))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1625,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_46)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_domain_1(u1_struct_0(sK1),X0_46) != u1_struct_0(k1_tex_2(sK1,X0_46))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1627,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,sK2))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_667,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1279,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1253,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1151,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_225,c_19,c_18,c_16])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | ~ r2_hidden(X0_46,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_46)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_46)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_46)) ),
    inference(subtyping,[status(esa)],[c_230])).

cnf(c_1095,plain,
    ( ~ m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_8])).

cnf(c_112,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v1_pre_topc(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_112,c_10,c_9])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_117,c_16])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_19])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0_46) = u1_struct_0(k1_tex_2(sK1,X0_46)) ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_713,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X3)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_16])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_19])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_46)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_707,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_12,negated_conjecture,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_661,negated_conjecture,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_288,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X1
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_289,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_281,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X1
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_282,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4327,c_3505,c_3490,c_2237,c_1876,c_1627,c_1279,c_1253,c_1151,c_1095,c_1077,c_713,c_707,c_661,c_289,c_282,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:05:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.57/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/0.98  
% 2.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/0.98  
% 2.57/0.98  ------  iProver source info
% 2.57/0.98  
% 2.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/0.98  git: non_committed_changes: false
% 2.57/0.98  git: last_make_outside_of_git: false
% 2.57/0.98  
% 2.57/0.98  ------ 
% 2.57/0.98  
% 2.57/0.98  ------ Input Options
% 2.57/0.98  
% 2.57/0.98  --out_options                           all
% 2.57/0.98  --tptp_safe_out                         true
% 2.57/0.98  --problem_path                          ""
% 2.57/0.98  --include_path                          ""
% 2.57/0.98  --clausifier                            res/vclausify_rel
% 2.57/0.98  --clausifier_options                    --mode clausify
% 2.57/0.98  --stdin                                 false
% 2.57/0.98  --stats_out                             all
% 2.57/0.98  
% 2.57/0.98  ------ General Options
% 2.57/0.98  
% 2.57/0.98  --fof                                   false
% 2.57/0.98  --time_out_real                         305.
% 2.57/0.98  --time_out_virtual                      -1.
% 2.57/0.98  --symbol_type_check                     false
% 2.57/0.98  --clausify_out                          false
% 2.57/0.98  --sig_cnt_out                           false
% 2.57/0.98  --trig_cnt_out                          false
% 2.57/0.98  --trig_cnt_out_tolerance                1.
% 2.57/0.98  --trig_cnt_out_sk_spl                   false
% 2.57/0.98  --abstr_cl_out                          false
% 2.57/0.98  
% 2.57/0.98  ------ Global Options
% 2.57/0.98  
% 2.57/0.98  --schedule                              default
% 2.57/0.98  --add_important_lit                     false
% 2.57/0.98  --prop_solver_per_cl                    1000
% 2.57/0.98  --min_unsat_core                        false
% 2.57/0.98  --soft_assumptions                      false
% 2.57/0.98  --soft_lemma_size                       3
% 2.57/0.98  --prop_impl_unit_size                   0
% 2.57/0.98  --prop_impl_unit                        []
% 2.57/0.98  --share_sel_clauses                     true
% 2.57/0.98  --reset_solvers                         false
% 2.57/0.98  --bc_imp_inh                            [conj_cone]
% 2.57/0.98  --conj_cone_tolerance                   3.
% 2.57/0.98  --extra_neg_conj                        none
% 2.57/0.98  --large_theory_mode                     true
% 2.57/0.98  --prolific_symb_bound                   200
% 2.57/0.98  --lt_threshold                          2000
% 2.57/0.98  --clause_weak_htbl                      true
% 2.57/0.98  --gc_record_bc_elim                     false
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing Options
% 2.57/0.98  
% 2.57/0.98  --preprocessing_flag                    true
% 2.57/0.98  --time_out_prep_mult                    0.1
% 2.57/0.98  --splitting_mode                        input
% 2.57/0.98  --splitting_grd                         true
% 2.57/0.98  --splitting_cvd                         false
% 2.57/0.98  --splitting_cvd_svl                     false
% 2.57/0.98  --splitting_nvd                         32
% 2.57/0.98  --sub_typing                            true
% 2.57/0.98  --prep_gs_sim                           true
% 2.57/0.98  --prep_unflatten                        true
% 2.57/0.98  --prep_res_sim                          true
% 2.57/0.98  --prep_upred                            true
% 2.57/0.98  --prep_sem_filter                       exhaustive
% 2.57/0.98  --prep_sem_filter_out                   false
% 2.57/0.98  --pred_elim                             true
% 2.57/0.98  --res_sim_input                         true
% 2.57/0.98  --eq_ax_congr_red                       true
% 2.57/0.98  --pure_diseq_elim                       true
% 2.57/0.98  --brand_transform                       false
% 2.57/0.98  --non_eq_to_eq                          false
% 2.57/0.98  --prep_def_merge                        true
% 2.57/0.98  --prep_def_merge_prop_impl              false
% 2.57/0.98  --prep_def_merge_mbd                    true
% 2.57/0.98  --prep_def_merge_tr_red                 false
% 2.57/0.98  --prep_def_merge_tr_cl                  false
% 2.57/0.98  --smt_preprocessing                     true
% 2.57/0.98  --smt_ac_axioms                         fast
% 2.57/0.98  --preprocessed_out                      false
% 2.57/0.98  --preprocessed_stats                    false
% 2.57/0.98  
% 2.57/0.98  ------ Abstraction refinement Options
% 2.57/0.98  
% 2.57/0.98  --abstr_ref                             []
% 2.57/0.98  --abstr_ref_prep                        false
% 2.57/0.98  --abstr_ref_until_sat                   false
% 2.57/0.98  --abstr_ref_sig_restrict                funpre
% 2.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.98  --abstr_ref_under                       []
% 2.57/0.98  
% 2.57/0.98  ------ SAT Options
% 2.57/0.98  
% 2.57/0.98  --sat_mode                              false
% 2.57/0.98  --sat_fm_restart_options                ""
% 2.57/0.98  --sat_gr_def                            false
% 2.57/0.98  --sat_epr_types                         true
% 2.57/0.98  --sat_non_cyclic_types                  false
% 2.57/0.98  --sat_finite_models                     false
% 2.57/0.98  --sat_fm_lemmas                         false
% 2.57/0.98  --sat_fm_prep                           false
% 2.57/0.98  --sat_fm_uc_incr                        true
% 2.57/0.98  --sat_out_model                         small
% 2.57/0.98  --sat_out_clauses                       false
% 2.57/0.98  
% 2.57/0.98  ------ QBF Options
% 2.57/0.98  
% 2.57/0.98  --qbf_mode                              false
% 2.57/0.98  --qbf_elim_univ                         false
% 2.57/0.98  --qbf_dom_inst                          none
% 2.57/0.98  --qbf_dom_pre_inst                      false
% 2.57/0.98  --qbf_sk_in                             false
% 2.57/0.98  --qbf_pred_elim                         true
% 2.57/0.98  --qbf_split                             512
% 2.57/0.98  
% 2.57/0.98  ------ BMC1 Options
% 2.57/0.98  
% 2.57/0.98  --bmc1_incremental                      false
% 2.57/0.98  --bmc1_axioms                           reachable_all
% 2.57/0.98  --bmc1_min_bound                        0
% 2.57/0.98  --bmc1_max_bound                        -1
% 2.57/0.98  --bmc1_max_bound_default                -1
% 2.57/0.98  --bmc1_symbol_reachability              true
% 2.57/0.98  --bmc1_property_lemmas                  false
% 2.57/0.98  --bmc1_k_induction                      false
% 2.57/0.98  --bmc1_non_equiv_states                 false
% 2.57/0.98  --bmc1_deadlock                         false
% 2.57/0.98  --bmc1_ucm                              false
% 2.57/0.98  --bmc1_add_unsat_core                   none
% 2.57/0.98  --bmc1_unsat_core_children              false
% 2.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/0.98  --bmc1_out_stat                         full
% 2.57/0.98  --bmc1_ground_init                      false
% 2.57/0.98  --bmc1_pre_inst_next_state              false
% 2.57/0.98  --bmc1_pre_inst_state                   false
% 2.57/0.98  --bmc1_pre_inst_reach_state             false
% 2.57/0.98  --bmc1_out_unsat_core                   false
% 2.57/0.98  --bmc1_aig_witness_out                  false
% 2.57/0.98  --bmc1_verbose                          false
% 2.57/0.98  --bmc1_dump_clauses_tptp                false
% 2.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.57/0.98  --bmc1_dump_file                        -
% 2.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.57/0.98  --bmc1_ucm_extend_mode                  1
% 2.57/0.98  --bmc1_ucm_init_mode                    2
% 2.57/0.98  --bmc1_ucm_cone_mode                    none
% 2.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.57/0.98  --bmc1_ucm_relax_model                  4
% 2.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/0.98  --bmc1_ucm_layered_model                none
% 2.57/0.98  --bmc1_ucm_max_lemma_size               10
% 2.57/0.98  
% 2.57/0.98  ------ AIG Options
% 2.57/0.98  
% 2.57/0.98  --aig_mode                              false
% 2.57/0.98  
% 2.57/0.98  ------ Instantiation Options
% 2.57/0.98  
% 2.57/0.98  --instantiation_flag                    true
% 2.57/0.98  --inst_sos_flag                         false
% 2.57/0.98  --inst_sos_phase                        true
% 2.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel_side                     num_symb
% 2.57/0.98  --inst_solver_per_active                1400
% 2.57/0.98  --inst_solver_calls_frac                1.
% 2.57/0.98  --inst_passive_queue_type               priority_queues
% 2.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/0.98  --inst_passive_queues_freq              [25;2]
% 2.57/0.98  --inst_dismatching                      true
% 2.57/0.98  --inst_eager_unprocessed_to_passive     true
% 2.57/0.98  --inst_prop_sim_given                   true
% 2.57/0.98  --inst_prop_sim_new                     false
% 2.57/0.98  --inst_subs_new                         false
% 2.57/0.98  --inst_eq_res_simp                      false
% 2.57/0.98  --inst_subs_given                       false
% 2.57/0.98  --inst_orphan_elimination               true
% 2.57/0.98  --inst_learning_loop_flag               true
% 2.57/0.98  --inst_learning_start                   3000
% 2.57/0.98  --inst_learning_factor                  2
% 2.57/0.98  --inst_start_prop_sim_after_learn       3
% 2.57/0.98  --inst_sel_renew                        solver
% 2.57/0.98  --inst_lit_activity_flag                true
% 2.57/0.98  --inst_restr_to_given                   false
% 2.57/0.98  --inst_activity_threshold               500
% 2.57/0.98  --inst_out_proof                        true
% 2.57/0.98  
% 2.57/0.98  ------ Resolution Options
% 2.57/0.98  
% 2.57/0.98  --resolution_flag                       true
% 2.57/0.98  --res_lit_sel                           adaptive
% 2.57/0.98  --res_lit_sel_side                      none
% 2.57/0.98  --res_ordering                          kbo
% 2.57/0.98  --res_to_prop_solver                    active
% 2.57/0.98  --res_prop_simpl_new                    false
% 2.57/0.98  --res_prop_simpl_given                  true
% 2.57/0.98  --res_passive_queue_type                priority_queues
% 2.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/0.98  --res_passive_queues_freq               [15;5]
% 2.57/0.98  --res_forward_subs                      full
% 2.57/0.98  --res_backward_subs                     full
% 2.57/0.98  --res_forward_subs_resolution           true
% 2.57/0.98  --res_backward_subs_resolution          true
% 2.57/0.98  --res_orphan_elimination                true
% 2.57/0.98  --res_time_limit                        2.
% 2.57/0.98  --res_out_proof                         true
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Options
% 2.57/0.98  
% 2.57/0.98  --superposition_flag                    true
% 2.57/0.98  --sup_passive_queue_type                priority_queues
% 2.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.57/0.98  --demod_completeness_check              fast
% 2.57/0.98  --demod_use_ground                      true
% 2.57/0.98  --sup_to_prop_solver                    passive
% 2.57/0.98  --sup_prop_simpl_new                    true
% 2.57/0.98  --sup_prop_simpl_given                  true
% 2.57/0.98  --sup_fun_splitting                     false
% 2.57/0.98  --sup_smt_interval                      50000
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Simplification Setup
% 2.57/0.98  
% 2.57/0.98  --sup_indices_passive                   []
% 2.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_full_bw                           [BwDemod]
% 2.57/0.98  --sup_immed_triv                        [TrivRules]
% 2.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_immed_bw_main                     []
% 2.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  
% 2.57/0.98  ------ Combination Options
% 2.57/0.98  
% 2.57/0.98  --comb_res_mult                         3
% 2.57/0.98  --comb_sup_mult                         2
% 2.57/0.98  --comb_inst_mult                        10
% 2.57/0.98  
% 2.57/0.98  ------ Debug Options
% 2.57/0.98  
% 2.57/0.98  --dbg_backtrace                         false
% 2.57/0.98  --dbg_dump_prop_clauses                 false
% 2.57/0.98  --dbg_dump_prop_clauses_file            -
% 2.57/0.98  --dbg_out_stat                          false
% 2.57/0.98  ------ Parsing...
% 2.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/0.98  ------ Proving...
% 2.57/0.98  ------ Problem Properties 
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  clauses                                 13
% 2.57/0.98  conjectures                             4
% 2.57/0.98  EPR                                     1
% 2.57/0.98  Horn                                    11
% 2.57/0.98  unary                                   4
% 2.57/0.98  binary                                  5
% 2.57/0.98  lits                                    28
% 2.57/0.98  lits eq                                 5
% 2.57/0.98  fd_pure                                 0
% 2.57/0.98  fd_pseudo                               0
% 2.57/0.98  fd_cond                                 0
% 2.57/0.98  fd_pseudo_cond                          0
% 2.57/0.98  AC symbols                              0
% 2.57/0.98  
% 2.57/0.98  ------ Schedule dynamic 5 is on 
% 2.57/0.98  
% 2.57/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  ------ 
% 2.57/0.98  Current options:
% 2.57/0.98  ------ 
% 2.57/0.98  
% 2.57/0.98  ------ Input Options
% 2.57/0.98  
% 2.57/0.98  --out_options                           all
% 2.57/0.98  --tptp_safe_out                         true
% 2.57/0.98  --problem_path                          ""
% 2.57/0.98  --include_path                          ""
% 2.57/0.98  --clausifier                            res/vclausify_rel
% 2.57/0.98  --clausifier_options                    --mode clausify
% 2.57/0.98  --stdin                                 false
% 2.57/0.98  --stats_out                             all
% 2.57/0.98  
% 2.57/0.98  ------ General Options
% 2.57/0.98  
% 2.57/0.98  --fof                                   false
% 2.57/0.98  --time_out_real                         305.
% 2.57/0.98  --time_out_virtual                      -1.
% 2.57/0.98  --symbol_type_check                     false
% 2.57/0.98  --clausify_out                          false
% 2.57/0.98  --sig_cnt_out                           false
% 2.57/0.98  --trig_cnt_out                          false
% 2.57/0.98  --trig_cnt_out_tolerance                1.
% 2.57/0.98  --trig_cnt_out_sk_spl                   false
% 2.57/0.98  --abstr_cl_out                          false
% 2.57/0.98  
% 2.57/0.98  ------ Global Options
% 2.57/0.98  
% 2.57/0.98  --schedule                              default
% 2.57/0.98  --add_important_lit                     false
% 2.57/0.98  --prop_solver_per_cl                    1000
% 2.57/0.98  --min_unsat_core                        false
% 2.57/0.98  --soft_assumptions                      false
% 2.57/0.98  --soft_lemma_size                       3
% 2.57/0.98  --prop_impl_unit_size                   0
% 2.57/0.98  --prop_impl_unit                        []
% 2.57/0.98  --share_sel_clauses                     true
% 2.57/0.98  --reset_solvers                         false
% 2.57/0.98  --bc_imp_inh                            [conj_cone]
% 2.57/0.98  --conj_cone_tolerance                   3.
% 2.57/0.98  --extra_neg_conj                        none
% 2.57/0.98  --large_theory_mode                     true
% 2.57/0.98  --prolific_symb_bound                   200
% 2.57/0.98  --lt_threshold                          2000
% 2.57/0.98  --clause_weak_htbl                      true
% 2.57/0.98  --gc_record_bc_elim                     false
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing Options
% 2.57/0.98  
% 2.57/0.98  --preprocessing_flag                    true
% 2.57/0.98  --time_out_prep_mult                    0.1
% 2.57/0.98  --splitting_mode                        input
% 2.57/0.98  --splitting_grd                         true
% 2.57/0.98  --splitting_cvd                         false
% 2.57/0.98  --splitting_cvd_svl                     false
% 2.57/0.98  --splitting_nvd                         32
% 2.57/0.98  --sub_typing                            true
% 2.57/0.98  --prep_gs_sim                           true
% 2.57/0.98  --prep_unflatten                        true
% 2.57/0.98  --prep_res_sim                          true
% 2.57/0.98  --prep_upred                            true
% 2.57/0.98  --prep_sem_filter                       exhaustive
% 2.57/0.98  --prep_sem_filter_out                   false
% 2.57/0.98  --pred_elim                             true
% 2.57/0.98  --res_sim_input                         true
% 2.57/0.98  --eq_ax_congr_red                       true
% 2.57/0.98  --pure_diseq_elim                       true
% 2.57/0.98  --brand_transform                       false
% 2.57/0.98  --non_eq_to_eq                          false
% 2.57/0.98  --prep_def_merge                        true
% 2.57/0.98  --prep_def_merge_prop_impl              false
% 2.57/0.98  --prep_def_merge_mbd                    true
% 2.57/0.98  --prep_def_merge_tr_red                 false
% 2.57/0.98  --prep_def_merge_tr_cl                  false
% 2.57/0.98  --smt_preprocessing                     true
% 2.57/0.98  --smt_ac_axioms                         fast
% 2.57/0.98  --preprocessed_out                      false
% 2.57/0.98  --preprocessed_stats                    false
% 2.57/0.98  
% 2.57/0.98  ------ Abstraction refinement Options
% 2.57/0.98  
% 2.57/0.98  --abstr_ref                             []
% 2.57/0.98  --abstr_ref_prep                        false
% 2.57/0.98  --abstr_ref_until_sat                   false
% 2.57/0.98  --abstr_ref_sig_restrict                funpre
% 2.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.98  --abstr_ref_under                       []
% 2.57/0.98  
% 2.57/0.98  ------ SAT Options
% 2.57/0.98  
% 2.57/0.98  --sat_mode                              false
% 2.57/0.98  --sat_fm_restart_options                ""
% 2.57/0.98  --sat_gr_def                            false
% 2.57/0.98  --sat_epr_types                         true
% 2.57/0.98  --sat_non_cyclic_types                  false
% 2.57/0.98  --sat_finite_models                     false
% 2.57/0.98  --sat_fm_lemmas                         false
% 2.57/0.98  --sat_fm_prep                           false
% 2.57/0.98  --sat_fm_uc_incr                        true
% 2.57/0.98  --sat_out_model                         small
% 2.57/0.98  --sat_out_clauses                       false
% 2.57/0.98  
% 2.57/0.98  ------ QBF Options
% 2.57/0.98  
% 2.57/0.98  --qbf_mode                              false
% 2.57/0.98  --qbf_elim_univ                         false
% 2.57/0.98  --qbf_dom_inst                          none
% 2.57/0.98  --qbf_dom_pre_inst                      false
% 2.57/0.98  --qbf_sk_in                             false
% 2.57/0.98  --qbf_pred_elim                         true
% 2.57/0.98  --qbf_split                             512
% 2.57/0.98  
% 2.57/0.98  ------ BMC1 Options
% 2.57/0.98  
% 2.57/0.98  --bmc1_incremental                      false
% 2.57/0.98  --bmc1_axioms                           reachable_all
% 2.57/0.98  --bmc1_min_bound                        0
% 2.57/0.98  --bmc1_max_bound                        -1
% 2.57/0.98  --bmc1_max_bound_default                -1
% 2.57/0.98  --bmc1_symbol_reachability              true
% 2.57/0.98  --bmc1_property_lemmas                  false
% 2.57/0.98  --bmc1_k_induction                      false
% 2.57/0.98  --bmc1_non_equiv_states                 false
% 2.57/0.98  --bmc1_deadlock                         false
% 2.57/0.98  --bmc1_ucm                              false
% 2.57/0.98  --bmc1_add_unsat_core                   none
% 2.57/0.98  --bmc1_unsat_core_children              false
% 2.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/0.98  --bmc1_out_stat                         full
% 2.57/0.98  --bmc1_ground_init                      false
% 2.57/0.98  --bmc1_pre_inst_next_state              false
% 2.57/0.98  --bmc1_pre_inst_state                   false
% 2.57/0.98  --bmc1_pre_inst_reach_state             false
% 2.57/0.98  --bmc1_out_unsat_core                   false
% 2.57/0.98  --bmc1_aig_witness_out                  false
% 2.57/0.98  --bmc1_verbose                          false
% 2.57/0.98  --bmc1_dump_clauses_tptp                false
% 2.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.57/0.98  --bmc1_dump_file                        -
% 2.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.57/0.98  --bmc1_ucm_extend_mode                  1
% 2.57/0.98  --bmc1_ucm_init_mode                    2
% 2.57/0.98  --bmc1_ucm_cone_mode                    none
% 2.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.57/0.98  --bmc1_ucm_relax_model                  4
% 2.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/0.98  --bmc1_ucm_layered_model                none
% 2.57/0.98  --bmc1_ucm_max_lemma_size               10
% 2.57/0.98  
% 2.57/0.98  ------ AIG Options
% 2.57/0.98  
% 2.57/0.98  --aig_mode                              false
% 2.57/0.98  
% 2.57/0.98  ------ Instantiation Options
% 2.57/0.98  
% 2.57/0.98  --instantiation_flag                    true
% 2.57/0.98  --inst_sos_flag                         false
% 2.57/0.98  --inst_sos_phase                        true
% 2.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel_side                     none
% 2.57/0.98  --inst_solver_per_active                1400
% 2.57/0.98  --inst_solver_calls_frac                1.
% 2.57/0.98  --inst_passive_queue_type               priority_queues
% 2.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/0.98  --inst_passive_queues_freq              [25;2]
% 2.57/0.98  --inst_dismatching                      true
% 2.57/0.98  --inst_eager_unprocessed_to_passive     true
% 2.57/0.98  --inst_prop_sim_given                   true
% 2.57/0.98  --inst_prop_sim_new                     false
% 2.57/0.98  --inst_subs_new                         false
% 2.57/0.98  --inst_eq_res_simp                      false
% 2.57/0.98  --inst_subs_given                       false
% 2.57/0.98  --inst_orphan_elimination               true
% 2.57/0.98  --inst_learning_loop_flag               true
% 2.57/0.98  --inst_learning_start                   3000
% 2.57/0.98  --inst_learning_factor                  2
% 2.57/0.98  --inst_start_prop_sim_after_learn       3
% 2.57/0.98  --inst_sel_renew                        solver
% 2.57/0.98  --inst_lit_activity_flag                true
% 2.57/0.98  --inst_restr_to_given                   false
% 2.57/0.98  --inst_activity_threshold               500
% 2.57/0.98  --inst_out_proof                        true
% 2.57/0.98  
% 2.57/0.98  ------ Resolution Options
% 2.57/0.98  
% 2.57/0.98  --resolution_flag                       false
% 2.57/0.98  --res_lit_sel                           adaptive
% 2.57/0.98  --res_lit_sel_side                      none
% 2.57/0.98  --res_ordering                          kbo
% 2.57/0.98  --res_to_prop_solver                    active
% 2.57/0.98  --res_prop_simpl_new                    false
% 2.57/0.98  --res_prop_simpl_given                  true
% 2.57/0.98  --res_passive_queue_type                priority_queues
% 2.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/0.98  --res_passive_queues_freq               [15;5]
% 2.57/0.98  --res_forward_subs                      full
% 2.57/0.98  --res_backward_subs                     full
% 2.57/0.98  --res_forward_subs_resolution           true
% 2.57/0.98  --res_backward_subs_resolution          true
% 2.57/0.98  --res_orphan_elimination                true
% 2.57/0.98  --res_time_limit                        2.
% 2.57/0.98  --res_out_proof                         true
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Options
% 2.57/0.98  
% 2.57/0.98  --superposition_flag                    true
% 2.57/0.98  --sup_passive_queue_type                priority_queues
% 2.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.57/0.98  --demod_completeness_check              fast
% 2.57/0.98  --demod_use_ground                      true
% 2.57/0.98  --sup_to_prop_solver                    passive
% 2.57/0.98  --sup_prop_simpl_new                    true
% 2.57/0.98  --sup_prop_simpl_given                  true
% 2.57/0.98  --sup_fun_splitting                     false
% 2.57/0.98  --sup_smt_interval                      50000
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Simplification Setup
% 2.57/0.98  
% 2.57/0.98  --sup_indices_passive                   []
% 2.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_full_bw                           [BwDemod]
% 2.57/0.98  --sup_immed_triv                        [TrivRules]
% 2.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_immed_bw_main                     []
% 2.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  
% 2.57/0.98  ------ Combination Options
% 2.57/0.98  
% 2.57/0.98  --comb_res_mult                         3
% 2.57/0.98  --comb_sup_mult                         2
% 2.57/0.98  --comb_inst_mult                        10
% 2.57/0.98  
% 2.57/0.98  ------ Debug Options
% 2.57/0.98  
% 2.57/0.98  --dbg_backtrace                         false
% 2.57/0.98  --dbg_dump_prop_clauses                 false
% 2.57/0.98  --dbg_dump_prop_clauses_file            -
% 2.57/0.98  --dbg_out_stat                          false
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  ------ Proving...
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  % SZS status Theorem for theBenchmark.p
% 2.57/0.98  
% 2.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/0.98  
% 2.57/0.98  fof(f2,axiom,(
% 2.57/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f12,plain,(
% 2.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.57/0.98    inference(ennf_transformation,[],[f2])).
% 2.57/0.98  
% 2.57/0.98  fof(f13,plain,(
% 2.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.57/0.98    inference(flattening,[],[f12])).
% 2.57/0.98  
% 2.57/0.98  fof(f35,plain,(
% 2.57/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f13])).
% 2.57/0.98  
% 2.57/0.98  fof(f3,axiom,(
% 2.57/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f14,plain,(
% 2.57/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.57/0.98    inference(ennf_transformation,[],[f3])).
% 2.57/0.98  
% 2.57/0.98  fof(f15,plain,(
% 2.57/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.57/0.98    inference(flattening,[],[f14])).
% 2.57/0.98  
% 2.57/0.98  fof(f36,plain,(
% 2.57/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f15])).
% 2.57/0.98  
% 2.57/0.98  fof(f8,conjecture,(
% 2.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f9,negated_conjecture,(
% 2.57/0.98    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 2.57/0.98    inference(negated_conjecture,[],[f8])).
% 2.57/0.98  
% 2.57/0.98  fof(f23,plain,(
% 2.57/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.57/0.98    inference(ennf_transformation,[],[f9])).
% 2.57/0.98  
% 2.57/0.98  fof(f24,plain,(
% 2.57/0.98    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.57/0.98    inference(flattening,[],[f23])).
% 2.57/0.98  
% 2.57/0.98  fof(f30,plain,(
% 2.57/0.98    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.57/0.98    introduced(choice_axiom,[])).
% 2.57/0.98  
% 2.57/0.98  fof(f29,plain,(
% 2.57/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.57/0.98    introduced(choice_axiom,[])).
% 2.57/0.98  
% 2.57/0.98  fof(f28,plain,(
% 2.57/0.98    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)) & ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.57/0.98    introduced(choice_axiom,[])).
% 2.57/0.98  
% 2.57/0.98  fof(f31,plain,(
% 2.57/0.98    ((k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) & ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f30,f29,f28])).
% 2.57/0.98  
% 2.57/0.98  fof(f47,plain,(
% 2.57/0.98    l1_pre_topc(sK1)),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  fof(f7,axiom,(
% 2.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f21,plain,(
% 2.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.57/0.98    inference(ennf_transformation,[],[f7])).
% 2.57/0.98  
% 2.57/0.98  fof(f22,plain,(
% 2.57/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.98    inference(flattening,[],[f21])).
% 2.57/0.98  
% 2.57/0.98  fof(f43,plain,(
% 2.57/0.98    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f22])).
% 2.57/0.98  
% 2.57/0.98  fof(f46,plain,(
% 2.57/0.98    v3_tdlat_3(sK1)),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  fof(f44,plain,(
% 2.57/0.98    ~v2_struct_0(sK1)),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  fof(f45,plain,(
% 2.57/0.98    v2_pre_topc(sK1)),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  fof(f5,axiom,(
% 2.57/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f17,plain,(
% 2.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.57/0.98    inference(ennf_transformation,[],[f5])).
% 2.57/0.98  
% 2.57/0.98  fof(f18,plain,(
% 2.57/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.98    inference(flattening,[],[f17])).
% 2.57/0.98  
% 2.57/0.98  fof(f27,plain,(
% 2.57/0.98    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.98    inference(nnf_transformation,[],[f18])).
% 2.57/0.98  
% 2.57/0.98  fof(f38,plain,(
% 2.57/0.98    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f27])).
% 2.57/0.98  
% 2.57/0.98  fof(f52,plain,(
% 2.57/0.98    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.98    inference(equality_resolution,[],[f38])).
% 2.57/0.98  
% 2.57/0.98  fof(f6,axiom,(
% 2.57/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f19,plain,(
% 2.57/0.98    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.57/0.98    inference(ennf_transformation,[],[f6])).
% 2.57/0.98  
% 2.57/0.98  fof(f20,plain,(
% 2.57/0.98    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.98    inference(flattening,[],[f19])).
% 2.57/0.98  
% 2.57/0.98  fof(f42,plain,(
% 2.57/0.98    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f20])).
% 2.57/0.98  
% 2.57/0.98  fof(f40,plain,(
% 2.57/0.98    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f20])).
% 2.57/0.98  
% 2.57/0.98  fof(f41,plain,(
% 2.57/0.98    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f20])).
% 2.57/0.98  
% 2.57/0.98  fof(f4,axiom,(
% 2.57/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f16,plain,(
% 2.57/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.57/0.98    inference(ennf_transformation,[],[f4])).
% 2.57/0.98  
% 2.57/0.98  fof(f37,plain,(
% 2.57/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f16])).
% 2.57/0.98  
% 2.57/0.98  fof(f51,plain,(
% 2.57/0.98    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  fof(f1,axiom,(
% 2.57/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f10,plain,(
% 2.57/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.57/0.98    inference(rectify,[],[f1])).
% 2.57/0.98  
% 2.57/0.98  fof(f11,plain,(
% 2.57/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.57/0.98    inference(ennf_transformation,[],[f10])).
% 2.57/0.98  
% 2.57/0.98  fof(f25,plain,(
% 2.57/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.57/0.98    introduced(choice_axiom,[])).
% 2.57/0.98  
% 2.57/0.98  fof(f26,plain,(
% 2.57/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f25])).
% 2.57/0.98  
% 2.57/0.98  fof(f33,plain,(
% 2.57/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f26])).
% 2.57/0.98  
% 2.57/0.98  fof(f50,plain,(
% 2.57/0.98    ~r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  fof(f32,plain,(
% 2.57/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f26])).
% 2.57/0.98  
% 2.57/0.98  fof(f49,plain,(
% 2.57/0.98    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  fof(f48,plain,(
% 2.57/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.57/0.98    inference(cnf_transformation,[],[f31])).
% 2.57/0.98  
% 2.57/0.98  cnf(c_669,plain,
% 2.57/0.98      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.57/0.98      theory(equality) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1032,plain,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X0_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X0_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_669]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1146,plain,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(X0_47,X0_46)
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(X0_47,X0_46)
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1032]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_4327,plain,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1146]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1145,plain,
% 2.57/0.98      ( X0_46 != X1_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X1_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = X0_46 ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_669]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1301,plain,
% 2.57/0.98      ( X0_46 != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = X0_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_3505,plain,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1301]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1307,plain,
% 2.57/0.98      ( X0_46 != X1_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X1_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = X0_46 ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_669]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1653,plain,
% 2.57/0.98      ( X0_46 != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = X0_46
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1307]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_3490,plain,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1653]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_3,plain,
% 2.57/0.98      ( m1_subset_1(X0,X1)
% 2.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.57/0.98      | ~ r2_hidden(X0,X2) ),
% 2.57/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_662,plain,
% 2.57/0.98      ( m1_subset_1(X0_46,X1_46)
% 2.57/0.98      | ~ m1_subset_1(X2_46,k1_zfmisc_1(X1_46))
% 2.57/0.98      | ~ r2_hidden(X0_46,X2_46) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1080,plain,
% 2.57/0.98      ( ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(X0_46))
% 2.57/0.98      | m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),X0_46)
% 2.57/0.98      | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_662]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_2237,plain,
% 2.57/0.98      ( ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),u1_struct_0(sK1))
% 2.57/0.98      | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1080]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_4,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.57/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.57/0.98      | ~ l1_pre_topc(X1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_16,negated_conjecture,
% 2.57/0.98      ( l1_pre_topc(sK1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_488,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.57/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.57/0.98      | sK1 != X1 ),
% 2.57/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_489,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.57/0.98      inference(unflattening,[status(thm)],[c_488]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_653,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | m1_subset_1(k2_pre_topc(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_489]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1874,plain,
% 2.57/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_46)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_653]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1876,plain,
% 2.57/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1874]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_673,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0_46,X1_46)
% 2.57/0.98      | m1_subset_1(X2_46,X3_46)
% 2.57/0.98      | X2_46 != X0_46
% 2.57/0.98      | X3_46 != X1_46 ),
% 2.57/0.98      theory(equality) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1053,plain,
% 2.57/0.98      ( m1_subset_1(X0_46,X1_46)
% 2.57/0.98      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X2_46)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | X0_46 != u1_struct_0(k1_tex_2(sK1,X2_46))
% 2.57/0.98      | X1_46 != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_673]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1278,plain,
% 2.57/0.98      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X1_46)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | X0_46 != u1_struct_0(k1_tex_2(sK1,X1_46))
% 2.57/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1053]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1625,plain,
% 2.57/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_46)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | k6_domain_1(u1_struct_0(sK1),X0_46) != u1_struct_0(k1_tex_2(sK1,X0_46))
% 2.57/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1278]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1627,plain,
% 2.57/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.57/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_1625]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_667,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1279,plain,
% 2.57/0.98      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_667]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1253,plain,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_667]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1151,plain,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_667]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_11,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.57/0.98      | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
% 2.57/0.98      | ~ v2_pre_topc(X1)
% 2.57/0.98      | ~ v3_tdlat_3(X1)
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | ~ l1_pre_topc(X1)
% 2.57/0.98      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) ),
% 2.57/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_17,negated_conjecture,
% 2.57/0.98      ( v3_tdlat_3(sK1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_224,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.57/0.98      | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
% 2.57/0.98      | ~ v2_pre_topc(X1)
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | ~ l1_pre_topc(X1)
% 2.57/0.98      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0))
% 2.57/0.98      | sK1 != X1 ),
% 2.57/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_225,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.57/0.98      | ~ r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
% 2.57/0.98      | ~ v2_pre_topc(sK1)
% 2.57/0.98      | v2_struct_0(sK1)
% 2.57/0.98      | ~ l1_pre_topc(sK1)
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) ),
% 2.57/0.98      inference(unflattening,[status(thm)],[c_224]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_19,negated_conjecture,
% 2.57/0.98      ( ~ v2_struct_0(sK1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_18,negated_conjecture,
% 2.57/0.98      ( v2_pre_topc(sK1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_229,plain,
% 2.57/0.98      ( ~ r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
% 2.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.57/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) ),
% 2.57/0.98      inference(global_propositional_subsumption,
% 2.57/0.98                [status(thm)],
% 2.57/0.98                [c_225,c_19,c_18,c_16]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_230,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.57/0.98      | ~ r2_hidden(X0,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1)) ),
% 2.57/0.98      inference(renaming,[status(thm)],[c_229]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_657,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 2.57/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
% 2.57/0.98      | ~ r2_hidden(X0_46,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_46)))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0_46)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X1_46)) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_230]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1095,plain,
% 2.57/0.98      ( ~ m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),u1_struct_0(sK1))
% 2.57/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.57/0.98      | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_657]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1077,plain,
% 2.57/0.98      ( ~ m1_subset_1(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),u1_struct_0(sK1))
% 2.57/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.57/0.98      | ~ r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))))) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_657]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_7,plain,
% 2.57/0.98      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.57/0.98      | v2_struct_0(X0)
% 2.57/0.98      | v2_struct_0(k1_tex_2(X0,X1))
% 2.57/0.98      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 2.57/0.98      | ~ l1_pre_topc(X0)
% 2.57/0.98      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 2.57/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_8,plain,
% 2.57/0.98      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.57/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.57/0.98      | v2_struct_0(X0)
% 2.57/0.98      | ~ l1_pre_topc(X0) ),
% 2.57/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_111,plain,
% 2.57/0.98      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.57/0.98      | v2_struct_0(X0)
% 2.57/0.98      | v2_struct_0(k1_tex_2(X0,X1))
% 2.57/0.98      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 2.57/0.98      | ~ l1_pre_topc(X0)
% 2.57/0.98      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 2.57/0.98      inference(global_propositional_subsumption,[status(thm)],[c_7,c_8]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_112,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | v2_struct_0(k1_tex_2(X1,X0))
% 2.57/0.98      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 2.57/0.98      | ~ l1_pre_topc(X1)
% 2.57/0.98      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.57/0.98      inference(renaming,[status(thm)],[c_111]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_10,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.57/0.98      | ~ l1_pre_topc(X1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_9,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | v1_pre_topc(k1_tex_2(X1,X0))
% 2.57/0.98      | ~ l1_pre_topc(X1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_117,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | ~ l1_pre_topc(X1)
% 2.57/0.98      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.57/0.98      inference(global_propositional_subsumption,
% 2.57/0.98                [status(thm)],
% 2.57/0.98                [c_112,c_10,c_9]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_452,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0))
% 2.57/0.98      | sK1 != X1 ),
% 2.57/0.98      inference(resolution_lifted,[status(thm)],[c_117,c_16]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_453,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.57/0.98      | v2_struct_0(sK1)
% 2.57/0.98      | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
% 2.57/0.98      inference(unflattening,[status(thm)],[c_452]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_457,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.57/0.98      | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
% 2.57/0.98      inference(global_propositional_subsumption,
% 2.57/0.98                [status(thm)],
% 2.57/0.98                [c_453,c_19]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_654,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 2.57/0.98      | k6_domain_1(u1_struct_0(sK1),X0_46) = u1_struct_0(k1_tex_2(sK1,X0_46)) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_457]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_713,plain,
% 2.57/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.57/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_654]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_5,plain,
% 2.57/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.57/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.57/0.98      | ~ l1_pre_topc(X1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_380,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X3)))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | ~ l1_pre_topc(X3)
% 2.57/0.98      | ~ l1_pre_topc(X1)
% 2.57/0.98      | X1 != X3
% 2.57/0.98      | k1_tex_2(X1,X0) != X2 ),
% 2.57/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_8]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_381,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),k1_zfmisc_1(u1_struct_0(X1)))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | ~ l1_pre_topc(X1) ),
% 2.57/0.98      inference(unflattening,[status(thm)],[c_380]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_410,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.57/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),k1_zfmisc_1(u1_struct_0(X1)))
% 2.57/0.98      | v2_struct_0(X1)
% 2.57/0.98      | sK1 != X1 ),
% 2.57/0.98      inference(resolution_lifted,[status(thm)],[c_381,c_16]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_411,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.57/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | v2_struct_0(sK1) ),
% 2.57/0.98      inference(unflattening,[status(thm)],[c_410]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_415,plain,
% 2.57/0.98      ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.57/0.98      inference(global_propositional_subsumption,
% 2.57/0.98                [status(thm)],
% 2.57/0.98                [c_411,c_19]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_416,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.57/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.57/0.98      inference(renaming,[status(thm)],[c_415]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_656,plain,
% 2.57/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 2.57/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_46)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_416]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_707,plain,
% 2.57/0.98      ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.57/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.57/0.98      inference(instantiation,[status(thm)],[c_656]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_12,negated_conjecture,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_661,negated_conjecture,
% 2.57/0.98      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1,plain,
% 2.57/0.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_13,negated_conjecture,
% 2.57/0.98      ( ~ r1_xboole_0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
% 2.57/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_288,plain,
% 2.57/0.98      ( r2_hidden(sK0(X0,X1),X1)
% 2.57/0.98      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X1
% 2.57/0.99      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_13]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_289,plain,
% 2.57/0.99      ( r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_288]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2,plain,
% 2.57/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_281,plain,
% 2.57/0.99      ( r2_hidden(sK0(X0,X1),X0)
% 2.57/0.99      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3)) != X1
% 2.57/0.99      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)) != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_282,plain,
% 2.57/0.99      ( r2_hidden(sK0(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2)),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3))),k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_281]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_14,negated_conjecture,
% 2.57/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.57/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_15,negated_conjecture,
% 2.57/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.57/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(contradiction,plain,
% 2.57/0.99      ( $false ),
% 2.57/0.99      inference(minisat,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4327,c_3505,c_3490,c_2237,c_1876,c_1627,c_1279,c_1253,
% 2.57/0.99                 c_1151,c_1095,c_1077,c_713,c_707,c_661,c_289,c_282,c_14,
% 2.57/0.99                 c_15]) ).
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/0.99  
% 2.57/0.99  ------                               Statistics
% 2.57/0.99  
% 2.57/0.99  ------ General
% 2.57/0.99  
% 2.57/0.99  abstr_ref_over_cycles:                  0
% 2.57/0.99  abstr_ref_under_cycles:                 0
% 2.57/0.99  gc_basic_clause_elim:                   0
% 2.57/0.99  forced_gc_time:                         0
% 2.57/0.99  parsing_time:                           0.012
% 2.57/0.99  unif_index_cands_time:                  0.
% 2.57/0.99  unif_index_add_time:                    0.
% 2.57/0.99  orderings_time:                         0.
% 2.57/0.99  out_proof_time:                         0.012
% 2.57/0.99  total_time:                             0.24
% 2.57/0.99  num_of_symbols:                         51
% 2.57/0.99  num_of_terms:                           3857
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing
% 2.57/0.99  
% 2.57/0.99  num_of_splits:                          0
% 2.57/0.99  num_of_split_atoms:                     0
% 2.57/0.99  num_of_reused_defs:                     0
% 2.57/0.99  num_eq_ax_congr_red:                    11
% 2.57/0.99  num_of_sem_filtered_clauses:            1
% 2.57/0.99  num_of_subtypes:                        2
% 2.57/0.99  monotx_restored_types:                  0
% 2.57/0.99  sat_num_of_epr_types:                   0
% 2.57/0.99  sat_num_of_non_cyclic_types:            0
% 2.57/0.99  sat_guarded_non_collapsed_types:        0
% 2.57/0.99  num_pure_diseq_elim:                    0
% 2.57/0.99  simp_replaced_by:                       0
% 2.57/0.99  res_preprocessed:                       84
% 2.57/0.99  prep_upred:                             0
% 2.57/0.99  prep_unflattend:                        27
% 2.57/0.99  smt_new_axioms:                         0
% 2.57/0.99  pred_elim_cands:                        3
% 2.57/0.99  pred_elim:                              6
% 2.57/0.99  pred_elim_cl:                           7
% 2.57/0.99  pred_elim_cycles:                       10
% 2.57/0.99  merged_defs:                            0
% 2.57/0.99  merged_defs_ncl:                        0
% 2.57/0.99  bin_hyper_res:                          0
% 2.57/0.99  prep_cycles:                            4
% 2.57/0.99  pred_elim_time:                         0.008
% 2.57/0.99  splitting_time:                         0.
% 2.57/0.99  sem_filter_time:                        0.
% 2.57/0.99  monotx_time:                            0.
% 2.57/0.99  subtype_inf_time:                       0.
% 2.57/0.99  
% 2.57/0.99  ------ Problem properties
% 2.57/0.99  
% 2.57/0.99  clauses:                                13
% 2.57/0.99  conjectures:                            4
% 2.57/0.99  epr:                                    1
% 2.57/0.99  horn:                                   11
% 2.57/0.99  ground:                                 4
% 2.57/0.99  unary:                                  4
% 2.57/0.99  binary:                                 5
% 2.57/0.99  lits:                                   28
% 2.57/0.99  lits_eq:                                5
% 2.57/0.99  fd_pure:                                0
% 2.57/0.99  fd_pseudo:                              0
% 2.57/0.99  fd_cond:                                0
% 2.57/0.99  fd_pseudo_cond:                         0
% 2.57/0.99  ac_symbols:                             0
% 2.57/0.99  
% 2.57/0.99  ------ Propositional Solver
% 2.57/0.99  
% 2.57/0.99  prop_solver_calls:                      30
% 2.57/0.99  prop_fast_solver_calls:                 701
% 2.57/0.99  smt_solver_calls:                       0
% 2.57/0.99  smt_fast_solver_calls:                  0
% 2.57/0.99  prop_num_of_clauses:                    1525
% 2.57/0.99  prop_preprocess_simplified:             4234
% 2.57/0.99  prop_fo_subsumed:                       21
% 2.57/0.99  prop_solver_time:                       0.
% 2.57/0.99  smt_solver_time:                        0.
% 2.57/0.99  smt_fast_solver_time:                   0.
% 2.57/0.99  prop_fast_solver_time:                  0.
% 2.57/0.99  prop_unsat_core_time:                   0.
% 2.57/0.99  
% 2.57/0.99  ------ QBF
% 2.57/0.99  
% 2.57/0.99  qbf_q_res:                              0
% 2.57/0.99  qbf_num_tautologies:                    0
% 2.57/0.99  qbf_prep_cycles:                        0
% 2.57/0.99  
% 2.57/0.99  ------ BMC1
% 2.57/0.99  
% 2.57/0.99  bmc1_current_bound:                     -1
% 2.57/0.99  bmc1_last_solved_bound:                 -1
% 2.57/0.99  bmc1_unsat_core_size:                   -1
% 2.57/0.99  bmc1_unsat_core_parents_size:           -1
% 2.57/0.99  bmc1_merge_next_fun:                    0
% 2.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.57/0.99  
% 2.57/0.99  ------ Instantiation
% 2.57/0.99  
% 2.57/0.99  inst_num_of_clauses:                    457
% 2.57/0.99  inst_num_in_passive:                    155
% 2.57/0.99  inst_num_in_active:                     274
% 2.57/0.99  inst_num_in_unprocessed:                27
% 2.57/0.99  inst_num_of_loops:                      285
% 2.57/0.99  inst_num_of_learning_restarts:          0
% 2.57/0.99  inst_num_moves_active_passive:          6
% 2.57/0.99  inst_lit_activity:                      0
% 2.57/0.99  inst_lit_activity_moves:                0
% 2.57/0.99  inst_num_tautologies:                   0
% 2.57/0.99  inst_num_prop_implied:                  0
% 2.57/0.99  inst_num_existing_simplified:           0
% 2.57/0.99  inst_num_eq_res_simplified:             0
% 2.57/0.99  inst_num_child_elim:                    0
% 2.57/0.99  inst_num_of_dismatching_blockings:      157
% 2.57/0.99  inst_num_of_non_proper_insts:           532
% 2.57/0.99  inst_num_of_duplicates:                 0
% 2.57/0.99  inst_inst_num_from_inst_to_res:         0
% 2.57/0.99  inst_dismatching_checking_time:         0.
% 2.57/0.99  
% 2.57/0.99  ------ Resolution
% 2.57/0.99  
% 2.57/0.99  res_num_of_clauses:                     0
% 2.57/0.99  res_num_in_passive:                     0
% 2.57/0.99  res_num_in_active:                      0
% 2.57/0.99  res_num_of_loops:                       88
% 2.57/0.99  res_forward_subset_subsumed:            97
% 2.57/0.99  res_backward_subset_subsumed:           0
% 2.57/0.99  res_forward_subsumed:                   0
% 2.57/0.99  res_backward_subsumed:                  0
% 2.57/0.99  res_forward_subsumption_resolution:     1
% 2.57/0.99  res_backward_subsumption_resolution:    0
% 2.57/0.99  res_clause_to_clause_subsumption:       257
% 2.57/0.99  res_orphan_elimination:                 0
% 2.57/0.99  res_tautology_del:                      73
% 2.57/0.99  res_num_eq_res_simplified:              0
% 2.57/0.99  res_num_sel_changes:                    0
% 2.57/0.99  res_moves_from_active_to_pass:          0
% 2.57/0.99  
% 2.57/0.99  ------ Superposition
% 2.57/0.99  
% 2.57/0.99  sup_time_total:                         0.
% 2.57/0.99  sup_time_generating:                    0.
% 2.57/0.99  sup_time_sim_full:                      0.
% 2.57/0.99  sup_time_sim_immed:                     0.
% 2.57/0.99  
% 2.57/0.99  sup_num_of_clauses:                     98
% 2.57/0.99  sup_num_in_active:                      53
% 2.57/0.99  sup_num_in_passive:                     45
% 2.57/0.99  sup_num_of_loops:                       56
% 2.57/0.99  sup_fw_superposition:                   49
% 2.57/0.99  sup_bw_superposition:                   50
% 2.57/0.99  sup_immediate_simplified:               12
% 2.57/0.99  sup_given_eliminated:                   0
% 2.57/0.99  comparisons_done:                       0
% 2.57/0.99  comparisons_avoided:                    0
% 2.57/0.99  
% 2.57/0.99  ------ Simplifications
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  sim_fw_subset_subsumed:                 0
% 2.57/0.99  sim_bw_subset_subsumed:                 1
% 2.57/0.99  sim_fw_subsumed:                        0
% 2.57/0.99  sim_bw_subsumed:                        0
% 2.57/0.99  sim_fw_subsumption_res:                 1
% 2.57/0.99  sim_bw_subsumption_res:                 0
% 2.57/0.99  sim_tautology_del:                      1
% 2.57/0.99  sim_eq_tautology_del:                   3
% 2.57/0.99  sim_eq_res_simp:                        0
% 2.57/0.99  sim_fw_demodulated:                     0
% 2.57/0.99  sim_bw_demodulated:                     3
% 2.57/0.99  sim_light_normalised:                   13
% 2.57/0.99  sim_joinable_taut:                      0
% 2.57/0.99  sim_joinable_simp:                      0
% 2.57/0.99  sim_ac_normalised:                      0
% 2.57/0.99  sim_smt_subsumption:                    0
% 2.57/0.99  
%------------------------------------------------------------------------------
