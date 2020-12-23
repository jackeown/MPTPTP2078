%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:52 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 670 expanded)
%              Number of leaves         :    9 ( 229 expanded)
%              Depth                    :   16
%              Number of atoms          :  383 (4359 expanded)
%              Number of equality atoms :   30 ( 184 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f29])).

fof(f29,plain,(
    ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(sK0,X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ v4_pre_topc(k1_connsp_2(sK0,X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_connsp_2)).

fof(f127,plain,(
    v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f125,f63])).

fof(f63,plain,(
    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f60,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ( ( ~ r2_hidden(X1,sK2(X0,X1,X3))
                          | ~ v4_pre_topc(sK2(X0,X1,X3),X0)
                          | ~ v3_pre_topc(sK2(X0,X1,X3),X0)
                          | ~ r2_hidden(sK2(X0,X1,X3),X3) )
                        & ( ( r2_hidden(X1,sK2(X0,X1,X3))
                            & v4_pre_topc(sK2(X0,X1,X3),X0)
                            & v3_pre_topc(sK2(X0,X1,X3),X0) )
                          | r2_hidden(sK2(X0,X1,X3),X3) )
                        & m1_subset_1(sK2(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ( k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
                    & ! [X6] :
                        ( ( ( r2_hidden(X6,sK3(X0,X1,X2))
                            | ~ r2_hidden(X1,X6)
                            | ~ v4_pre_topc(X6,X0)
                            | ~ v3_pre_topc(X6,X0) )
                          & ( ( r2_hidden(X1,X6)
                              & v4_pre_topc(X6,X0)
                              & v3_pre_topc(X6,X0) )
                            | ~ r2_hidden(X6,sK3(X0,X1,X2)) ) )
                        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f21,f20])).

fof(f20,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X1,X4)
            | ~ v4_pre_topc(X4,X0)
            | ~ v3_pre_topc(X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( ( r2_hidden(X1,X4)
              & v4_pre_topc(X4,X0)
              & v3_pre_topc(X4,X0) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r2_hidden(X1,sK2(X0,X1,X3))
          | ~ v4_pre_topc(sK2(X0,X1,X3),X0)
          | ~ v3_pre_topc(sK2(X0,X1,X3),X0)
          | ~ r2_hidden(sK2(X0,X1,X3),X3) )
        & ( ( r2_hidden(X1,sK2(X0,X1,X3))
            & v4_pre_topc(sK2(X0,X1,X3),X0)
            & v3_pre_topc(sK2(X0,X1,X3),X0) )
          | r2_hidden(sK2(X0,X1,X3),X3) )
        & m1_subset_1(sK2(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k6_setfam_1(u1_struct_0(X0),X5) = X2
          & ! [X6] :
              ( ( ( r2_hidden(X6,X5)
                  | ~ r2_hidden(X1,X6)
                  | ~ v4_pre_topc(X6,X0)
                  | ~ v3_pre_topc(X6,X0) )
                & ( ( r2_hidden(X1,X6)
                    & v4_pre_topc(X6,X0)
                    & v3_pre_topc(X6,X0) )
                  | ~ r2_hidden(X6,X5) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
        & ! [X6] :
            ( ( ( r2_hidden(X6,sK3(X0,X1,X2))
                | ~ r2_hidden(X1,X6)
                | ~ v4_pre_topc(X6,X0)
                | ~ v3_pre_topc(X6,X0) )
              & ( ( r2_hidden(X1,X6)
                  & v4_pre_topc(X6,X0)
                  & v3_pre_topc(X6,X0) )
                | ~ r2_hidden(X6,sK3(X0,X1,X2)) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ? [X4] :
                          ( ( ~ r2_hidden(X1,X4)
                            | ~ v4_pre_topc(X4,X0)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ r2_hidden(X4,X3) )
                          & ( ( r2_hidden(X1,X4)
                              & v4_pre_topc(X4,X0)
                              & v3_pre_topc(X4,X0) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ? [X5] :
                      ( k6_setfam_1(u1_struct_0(X0),X5) = X2
                      & ! [X6] :
                          ( ( ( r2_hidden(X6,X5)
                              | ~ r2_hidden(X1,X6)
                              | ~ v4_pre_topc(X6,X0)
                              | ~ v3_pre_topc(X6,X0) )
                            & ( ( r2_hidden(X1,X6)
                                & v4_pre_topc(X6,X0)
                                & v3_pre_topc(X6,X0) )
                              | ~ r2_hidden(X6,X5) ) )
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ? [X4] :
                          ( ( ~ r2_hidden(X1,X4)
                            | ~ v4_pre_topc(X4,X0)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ r2_hidden(X4,X3) )
                          & ( ( r2_hidden(X1,X4)
                              & v4_pre_topc(X4,X0)
                              & v3_pre_topc(X4,X0) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ? [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                      & ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ~ r2_hidden(X1,X4)
                              | ~ v4_pre_topc(X4,X0)
                              | ~ v3_pre_topc(X4,X0) )
                            & ( ( r2_hidden(X1,X4)
                                & v4_pre_topc(X4,X0)
                                & v3_pre_topc(X4,X0) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_connsp_2(X0,X1) = X2
                  | ! [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) != X2
                      | ? [X4] :
                          ( ( ~ r2_hidden(X1,X4)
                            | ~ v4_pre_topc(X4,X0)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ r2_hidden(X4,X3) )
                          & ( ( r2_hidden(X1,X4)
                              & v4_pre_topc(X4,X0)
                              & v3_pre_topc(X4,X0) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
                & ( ? [X3] :
                      ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                      & ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ~ r2_hidden(X1,X4)
                              | ~ v4_pre_topc(X4,X0)
                              | ~ v3_pre_topc(X4,X0) )
                            & ( ( r2_hidden(X1,X4)
                                & v4_pre_topc(X4,X0)
                                & v3_pre_topc(X4,X0) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | k1_connsp_2(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_2)).

fof(f60,plain,(
    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,(
    v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f26,f27,f61,f123,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK4(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f23])).

% (19266)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (19262)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_pre_topc)).

fof(f123,plain,(
    ~ m1_subset_1(sK4(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f60,f122,f89,f53])).

fof(f53,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X6,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( v4_pre_topc(X6,X0)
      | ~ r2_hidden(X6,sK3(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    r2_hidden(sK4(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | r2_hidden(sK4(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(forward_demodulation,[],[f87,f63])).

fof(f87,plain,
    ( r2_hidden(sK4(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) ),
    inference(resolution,[],[f61,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK4(sK0,X0),X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f56,f26])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f27,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f122,plain,(
    ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f121,f61])).

fof(f121,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f120,f29])).

fof(f120,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v4_pre_topc(sK4(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) ),
    inference(superposition,[],[f59,f63])).

fof(f59,plain,(
    ! [X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v4_pre_topc(sK4(sK0,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f57,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(sK4(sK0,X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f27,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f60,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
