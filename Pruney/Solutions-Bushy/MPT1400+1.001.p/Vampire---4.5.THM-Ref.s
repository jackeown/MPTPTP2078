%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1400+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  147 (24170 expanded)
%              Number of leaves         :   15 (8130 expanded)
%              Depth                    :   33
%              Number of atoms          :  924 (161882 expanded)
%              Number of equality atoms :  100 (10857 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f580,plain,(
    $false ),
    inference(subsumption_resolution,[],[f579,f536])).

fof(f536,plain,(
    v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0) ),
    inference(unit_resulting_resolution,[],[f520,f445])).

fof(f445,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f219,f222])).

fof(f222,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f140,f214])).

fof(f214,plain,(
    k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f213,f51])).

fof(f51,plain,(
    ~ r2_hidden(sK1,k1_connsp_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(sK0,X1))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ~ r2_hidden(X1,k1_connsp_2(sK0,X1))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(sK1,k1_connsp_2(sK0,sK1))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f213,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(forward_demodulation,[],[f212,f142])).

fof(f142,plain,(
    k1_connsp_2(sK0,sK1) = k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(forward_demodulation,[],[f138,f109])).

fof(f109,plain,(
    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f105,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,(
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

fof(f35,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f105,plain,(
    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f138,plain,(
    k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) = k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f107,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f107,plain,(
    m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f105,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f212,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1))
    | r2_hidden(sK1,k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f211,f51])).

fof(f211,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1))
    | r2_hidden(sK1,k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1))
    | r2_hidden(sK1,k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(resolution,[],[f197,f102])).

fof(f102,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,sK7(X0,X5))
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK7(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
                  & r2_hidden(sK6(X0,X1),X0) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK5(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK7(X0,X5))
                    & r2_hidden(sK7(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK5(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK5(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK5(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK7(X0,X5))
        & r2_hidden(sK7(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f197,plain,(
    ! [X4] :
      ( r2_hidden(sK1,sK7(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),X4))
      | r2_hidden(X4,k1_connsp_2(sK0,sK1))
      | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f196,f182])).

fof(f182,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_connsp_2(sK0,sK1))
      | m1_subset_1(sK7(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f181,f142])).

fof(f181,plain,(
    ! [X4] :
      ( m1_subset_1(sK7(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))))
      | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ) ),
    inference(resolution,[],[f140,f103])).

fof(f103,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),X0)
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK7(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f196,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_connsp_2(sK0,sK1))
      | ~ m1_subset_1(sK7(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,sK7(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),X4))
      | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f193,f142])).

fof(f193,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK7(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,sK7(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),X4))
      | r2_hidden(X4,k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))))
      | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ) ),
    inference(resolution,[],[f130,f103])).

fof(f130,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f129,f47])).

fof(f129,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f48])).

fof(f128,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f49])).

fof(f127,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f50])).

fof(f114,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,X2)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f89])).

fof(f89,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X6)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X1,X6)
      | ~ r2_hidden(X6,sK3(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f107,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f219,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k1_xboole_0)
      | v4_pre_topc(X1,sK0) ) ),
    inference(backward_demodulation,[],[f126,f214])).

fof(f126,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f125,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f124,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f49])).

fof(f123,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X1,sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f90])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X6,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f520,plain,(
    r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f50,f489,f473])).

fof(f473,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,sK4(sK0,X0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f472,f361])).

fof(f361,plain,(
    ! [X1] :
      ( v3_pre_topc(sK4(sK0,X1,k1_xboole_0),sK0)
      | r2_hidden(sK4(sK0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f360,f47])).

fof(f360,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,k1_xboole_0),k1_xboole_0)
      | v3_pre_topc(sK4(sK0,X1,k1_xboole_0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f359,f48])).

fof(f359,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,k1_xboole_0),k1_xboole_0)
      | v3_pre_topc(sK4(sK0,X1,k1_xboole_0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f348,f49])).

fof(f348,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,k1_xboole_0),k1_xboole_0)
      | v3_pre_topc(sK4(sK0,X1,k1_xboole_0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f215,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | v3_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ( ( ~ r2_hidden(X1,sK4(X0,X1,X2))
                  | ~ v4_pre_topc(sK4(X0,X1,X2),X0)
                  | ~ v3_pre_topc(sK4(X0,X1,X2),X0)
                  | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                & ( ( r2_hidden(X1,sK4(X0,X1,X2))
                    & v4_pre_topc(sK4(X0,X1,X2),X0)
                    & v3_pre_topc(sK4(X0,X1,X2),X0) )
                  | r2_hidden(sK4(X0,X1,X2),X2) )
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X1,X3)
              & v4_pre_topc(X3,X0)
              & v3_pre_topc(X3,X0) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r2_hidden(X1,sK4(X0,X1,X2))
          | ~ v4_pre_topc(sK4(X0,X1,X2),X0)
          | ~ v3_pre_topc(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(X1,sK4(X0,X1,X2))
            & v4_pre_topc(sK4(X0,X1,X2),X0)
            & v3_pre_topc(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ r2_hidden(X3,X2) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ r2_hidden(X3,X2) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( r2_hidden(X3,X2)
                  <~> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != X2
              | ? [X3] :
                  ( ( r2_hidden(X3,X2)
                  <~> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f215,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f107,f214])).

fof(f472,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK4(sK0,X0,k1_xboole_0),sK0)
      | r2_hidden(sK4(sK0,X0,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK1,sK4(sK0,X0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f466,f364])).

fof(f364,plain,(
    ! [X2] :
      ( v4_pre_topc(sK4(sK0,X2,k1_xboole_0),sK0)
      | r2_hidden(sK4(sK0,X2,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f363,f47])).

fof(f363,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,X2,k1_xboole_0),k1_xboole_0)
      | v4_pre_topc(sK4(sK0,X2,k1_xboole_0),sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f362,f48])).

fof(f362,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,X2,k1_xboole_0),k1_xboole_0)
      | v4_pre_topc(sK4(sK0,X2,k1_xboole_0),sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f349,f49])).

fof(f349,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,X2,k1_xboole_0),k1_xboole_0)
      | v4_pre_topc(sK4(sK0,X2,k1_xboole_0),sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f215,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | v4_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f466,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_pre_topc(sK4(sK0,X0,k1_xboole_0),sK0)
      | ~ v3_pre_topc(sK4(sK0,X0,k1_xboole_0),sK0)
      | r2_hidden(sK4(sK0,X0,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK1,sK4(sK0,X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f358,f221])).

fof(f221,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(backward_demodulation,[],[f134,f214])).

fof(f134,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f133,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f48])).

fof(f132,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f49])).

fof(f131,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f88])).

fof(f88,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X6)
      | ~ v4_pre_topc(X6,X0)
      | ~ v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,sK3(X0,X1,X2))
      | ~ r2_hidden(X1,X6)
      | ~ v4_pre_topc(X6,X0)
      | ~ v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f358,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f357,f47])).

fof(f357,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f356,f48])).

fof(f356,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f347,f49])).

fof(f347,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f215,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK4(X0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f489,plain,(
    r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f488,f452])).

fof(f452,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(sK1,X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f220,f222])).

fof(f220,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(sK1,X2) ) ),
    inference(backward_demodulation,[],[f130,f214])).

fof(f488,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f367,f50])).

fof(f367,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,sK4(sK0,X3,k1_xboole_0))
      | r2_hidden(sK4(sK0,X3,k1_xboole_0),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f366,f47])).

% (17826)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f366,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK0,X3,k1_xboole_0),k1_xboole_0)
      | r2_hidden(X3,sK4(sK0,X3,k1_xboole_0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f365,f48])).

fof(f365,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK0,X3,k1_xboole_0),k1_xboole_0)
      | r2_hidden(X3,sK4(sK0,X3,k1_xboole_0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f350,f49])).

fof(f350,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK0,X3,k1_xboole_0),k1_xboole_0)
      | r2_hidden(X3,sK4(sK0,X3,k1_xboole_0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f215,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | r2_hidden(X1,sK4(X0,X1,k1_xboole_0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | r2_hidden(X1,sK4(X0,X1,X2))
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f579,plain,(
    ~ v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f489,f520,f215,f535,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | ~ v3_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | ~ r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(X1,sK4(X0,X1,k1_xboole_0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ r2_hidden(X1,sK4(X0,X1,X2))
      | ~ v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f535,plain,(
    v3_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0) ),
    inference(unit_resulting_resolution,[],[f520,f436])).

fof(f436,plain,(
    ! [X0] :
      ( v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f431])).

fof(f431,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f218,f222])).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_xboole_0)
      | v3_pre_topc(X0,sK0) ) ),
    inference(backward_demodulation,[],[f122,f214])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f91])).

fof(f91,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( v3_pre_topc(X6,X0)
      | ~ r2_hidden(X6,sK3(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

%------------------------------------------------------------------------------
