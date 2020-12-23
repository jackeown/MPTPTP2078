%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:48 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 340 expanded)
%              Number of clauses        :   40 (  65 expanded)
%              Number of leaves         :    8 ( 118 expanded)
%              Depth                    :   21
%              Number of atoms          :  400 (3145 expanded)
%              Number of equality atoms :   48 ( 355 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK4(X2)) = k6_domain_1(u1_struct_0(X0),X2)
        & v4_pre_topc(sK4(X2),X0)
        & m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK3,X0)
        & ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),sK3,X3) = k6_domain_1(u1_struct_0(X0),X2)
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,sK3)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(sK2),X1,X3) = k6_domain_1(u1_struct_0(sK2),X2)
                  & v4_pre_topc(X3,sK2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & ! [X2] :
        ( ( k9_subset_1(u1_struct_0(sK2),sK3,sK4(X2)) = k6_domain_1(u1_struct_0(sK2),X2)
          & v4_pre_topc(sK4(X2),sK2)
          & m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK2))) )
        | ~ r2_hidden(X2,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f22,f21,f20])).

fof(f39,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4(X2)) = k6_domain_1(u1_struct_0(sK2),X2)
      | ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
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

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK1(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK1(X0,X1))
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK1(X0,X1))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK0(X0),X0)
            & v4_pre_topc(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f24,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2] :
      ( v4_pre_topc(sK4(X2),sK2)
      | ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2] :
      ( m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(X0)) = k6_domain_1(u1_struct_0(sK2),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_245,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_246,plain,
    ( r2_hidden(sK1(sK2,X0),X0)
    | v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_250,plain,
    ( r2_hidden(sK1(sK2,X0),X0)
    | v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_16,c_15])).

cnf(c_327,plain,
    ( r2_hidden(sK1(sK2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_250])).

cnf(c_328,plain,
    ( r2_hidden(sK1(sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_330,plain,
    ( r2_hidden(sK1(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_12])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(X0)) = k6_domain_1(u1_struct_0(sK2),X0)
    | sK1(sK2,sK3) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_330])).

cnf(c_378,plain,
    ( ~ m1_subset_1(sK1(sK2,sK3),u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(sK1(sK2,sK3))) = k6_domain_1(u1_struct_0(sK2),sK1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_4,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK1(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v4_pre_topc(sK4(X0),sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_187,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v3_tdlat_3(X2)
    | sK4(X0) != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_188,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK4(X0),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_14,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_192,plain,
    ( v3_pre_topc(sK4(X0),sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_188,c_15,c_14,c_13,c_11])).

cnf(c_193,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v3_pre_topc(sK4(X0),sK2) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_212,plain,
    ( ~ r2_hidden(X0,sK3)
    | v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | k6_domain_1(u1_struct_0(X2),sK1(X2,X1)) != k9_subset_1(u1_struct_0(X2),X1,X3)
    | sK4(X0) != X3
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_193])).

cnf(c_213,plain,
    ( ~ r2_hidden(X0,sK3)
    | v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK1(sK2,X1)) != k9_subset_1(u1_struct_0(sK2),X1,sK4(X0)) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,sK3)
    | v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK1(sK2,X1)) != k9_subset_1(u1_struct_0(sK2),X1,sK4(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_213,c_16,c_15,c_13,c_11])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),X1,sK4(X0)) != k6_domain_1(u1_struct_0(sK2),sK1(sK2,X1))
    | sK2 != sK2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_217])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(X0)) != k6_domain_1(u1_struct_0(sK2),sK1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(X0)) != k6_domain_1(u1_struct_0(sK2),sK1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_12])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(X0)) != k6_domain_1(u1_struct_0(sK2),sK1(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(X0)) != k6_domain_1(u1_struct_0(sK2),sK1(sK2,sK3))
    | sK1(sK2,sK3) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_330])).

cnf(c_359,plain,
    ( ~ m1_subset_1(sK1(sK2,sK3),u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4(sK1(sK2,sK3))) != k6_domain_1(u1_struct_0(sK2),sK1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_6,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_266,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_267,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_271,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_267,c_16,c_15])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),u1_struct_0(sK2))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_271])).

cnf(c_317,plain,
    ( m1_subset_1(sK1(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_378,c_359,c_317,c_12])).


%------------------------------------------------------------------------------
