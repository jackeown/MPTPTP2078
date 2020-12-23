%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t30_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 4.17s
% Output     : Refutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  172 (3381 expanded)
%              Number of leaves         :   18 (1057 expanded)
%              Depth                    :   26
%              Number of atoms          : 1027 (21827 expanded)
%              Number of equality atoms :  102 (1288 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12669,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12668,f9871])).

fof(f9871,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f9866,f302])).

fof(f302,plain,(
    m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f301,f76])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f51,f50])).

fof(f50,plain,
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

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1,k1_connsp_2(X0,sK1))
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k1_connsp_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',t30_connsp_2)).

fof(f301,plain,
    ( m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f300,f77])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f300,plain,
    ( m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f299,f78])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f299,plain,
    ( m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f262])).

fof(f262,plain,(
    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f261,f76])).

fof(f261,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f77])).

fof(f260,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f242,f78])).

fof(f242,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',dt_k1_connsp_2)).

fof(f79,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f253,plain,
    ( m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f55,f57,f56])).

fof(f56,plain,(
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

fof(f57,plain,(
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

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',d7_connsp_2)).

fof(f9866,plain,(
    k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f9865,f80])).

fof(f80,plain,(
    ~ r2_hidden(sK1,k1_connsp_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f9865,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(forward_demodulation,[],[f9858,f411])).

fof(f411,plain,(
    k1_connsp_2(sK0,sK1) = k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(forward_demodulation,[],[f375,f286])).

fof(f286,plain,(
    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f285,f76])).

fof(f285,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f284,f77])).

fof(f284,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f283,f78])).

fof(f283,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f262])).

fof(f248,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f375,plain,(
    k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(resolution,[],[f302,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k1_setfam_1(X1) = k6_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',redefinition_k6_setfam_1)).

fof(f9858,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1))
    | r2_hidden(sK1,k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))) ),
    inference(duplicate_literal_removal,[],[f9851])).

fof(f9851,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1))
    | r2_hidden(sK1,k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(resolution,[],[f1545,f143])).

fof(f143,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK8(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK8(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK6(X0,X1),sK7(X0,X1))
                  & r2_hidden(sK7(X0,X1),X0) )
                | ~ r2_hidden(sK6(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK6(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK6(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK8(X0,X5))
                    & r2_hidden(sK8(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f66,f69,f68,f67])).

fof(f67,plain,(
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
              ( ~ r2_hidden(sK6(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK6(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK8(X0,X5))
        & r2_hidden(sK8(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',d1_setfam_1)).

fof(f1545,plain,
    ( ~ r2_hidden(sK8(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK1),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1538,f80])).

fof(f1538,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | ~ r2_hidden(sK8(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),sK1),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | k1_xboole_0 = sK3(sK0,sK1,k1_connsp_2(sK0,sK1)) ),
    inference(superposition,[],[f527,f411])).

fof(f527,plain,(
    ! [X26] :
      ( r2_hidden(sK1,k1_setfam_1(X26))
      | ~ r2_hidden(sK8(X26,sK1),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | k1_xboole_0 = X26 ) ),
    inference(subsumption_resolution,[],[f505,f377])).

fof(f377,plain,(
    ! [X6] :
      ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ) ),
    inference(resolution,[],[f302,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',t4_subset)).

fof(f505,plain,(
    ! [X26] :
      ( ~ r2_hidden(sK8(X26,sK1),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(sK8(X26,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,k1_setfam_1(X26))
      | k1_xboole_0 = X26 ) ),
    inference(resolution,[],[f290,f142])).

fof(f142,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK8(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK8(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f290,plain,(
    ! [X6] :
      ( r2_hidden(sK1,X6)
      | ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f289,f76])).

fof(f289,plain,(
    ! [X6] :
      ( r2_hidden(sK1,X6)
      | ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f77])).

fof(f288,plain,(
    ! [X6] :
      ( r2_hidden(sK1,X6)
      | ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f78])).

fof(f287,plain,(
    ! [X6] :
      ( r2_hidden(sK1,X6)
      | ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f250,f262])).

fof(f250,plain,(
    ! [X6] :
      ( r2_hidden(sK1,X6)
      | ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f79,f129])).

fof(f129,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X1,X6)
      | ~ r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f12668,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f11015,f12597])).

fof(f12597,plain,(
    r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f11017,f9871])).

fof(f11017,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f10088])).

fof(f10088,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f9866,f2166])).

fof(f2166,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f2165,f317])).

fof(f317,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f316,f76])).

fof(f316,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f315,f77])).

fof(f315,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f78])).

fof(f258,plain,
    ( m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f61,plain,(
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

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',t28_connsp_2)).

fof(f2165,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f2164,f308])).

fof(f308,plain,
    ( r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f307,f76])).

fof(f307,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f306,f77])).

fof(f306,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f78])).

fof(f255,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK4(X0,X1,k1_xboole_0))
      | r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | r2_hidden(X1,sK4(X0,X1,X2))
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2164,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f2154,f782])).

fof(f782,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v3_pre_topc(sK4(sK0,X1,k1_xboole_0),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(sK0,X1,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f204,f118])).

fof(f204,plain,(
    ! [X24] :
      ( ~ m1_subset_1(X24,u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X24,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v3_pre_topc(sK4(sK0,X24,k1_xboole_0),sK0) ) ),
    inference(subsumption_resolution,[],[f203,f77])).

fof(f203,plain,(
    ! [X24] :
      ( v3_pre_topc(sK4(sK0,X24,k1_xboole_0),sK0)
      | r2_hidden(sK4(sK0,X24,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X24,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f78])).

fof(f160,plain,(
    ! [X24] :
      ( v3_pre_topc(sK4(sK0,X24,k1_xboole_0),sK0)
      | r2_hidden(sK4(sK0,X24,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X24,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f76,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2154,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ v3_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f344,f311])).

fof(f311,plain,
    ( v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f310,f76])).

fof(f310,plain,
    ( v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f309,f77])).

fof(f309,plain,
    ( v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f256,f78])).

fof(f256,plain,
    ( v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f344,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f343,f76])).

fof(f343,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f342,f77])).

fof(f342,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f341,f78])).

fof(f341,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f331,f79])).

fof(f331,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f262,f128])).

fof(f128,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ r2_hidden(X1,X6)
      | ~ v4_pre_topc(X6,X0)
      | ~ v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f11015,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f10194])).

fof(f10194,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f9866,f3697])).

fof(f3697,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f3690,f1122])).

fof(f1122,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f1077,f511])).

fof(f511,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f493,f377])).

fof(f493,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f290,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',t7_boole)).

fof(f1077,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | r2_hidden(sK1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f510,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',t2_subset)).

fof(f510,plain,(
    ! [X5] :
      ( m1_subset_1(sK1,X5)
      | ~ r2_hidden(X5,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f492,f377])).

fof(f492,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK1,X5) ) ),
    inference(resolution,[],[f290,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t30_connsp_2.p',t1_subset)).

fof(f3690,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0)) ),
    inference(resolution,[],[f947,f79])).

fof(f947,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))
      | ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f946,f118])).

fof(f946,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
      | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))
      | ~ m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f934,f193])).

fof(f193,plain,(
    ! [X19,X18] :
      ( v3_pre_topc(X18,sK0)
      | ~ r2_hidden(X18,sK3(sK0,X19,k1_connsp_2(sK0,X19)))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f192,f163])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f162,f77])).

fof(f162,plain,(
    ! [X0] :
      ( m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f78])).

fof(f145,plain,(
    ! [X0] :
      ( m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f76,f113])).

fof(f192,plain,(
    ! [X19,X18] :
      ( v3_pre_topc(X18,sK0)
      | ~ r2_hidden(X18,sK3(sK0,X19,k1_connsp_2(sK0,X19)))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_connsp_2(sK0,X19),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f191,f77])).

fof(f191,plain,(
    ! [X19,X18] :
      ( v3_pre_topc(X18,sK0)
      | ~ r2_hidden(X18,sK3(sK0,X19,k1_connsp_2(sK0,X19)))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_connsp_2(sK0,X19),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f78])).

fof(f155,plain,(
    ! [X19,X18] :
      ( v3_pre_topc(X18,sK0)
      | ~ r2_hidden(X18,sK3(sK0,X19,k1_connsp_2(sK0,X19)))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_connsp_2(sK0,X19),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X19,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f76,f131])).

fof(f131,plain,(
    ! [X6,X0,X1] :
      ( v3_pre_topc(X6,X0)
      | ~ r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f934,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
      | ~ v3_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
      | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))
      | ~ m1_subset_1(sK4(sK0,sK1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f305,f190])).

fof(f190,plain,(
    ! [X17,X16] :
      ( v4_pre_topc(X16,sK0)
      | ~ r2_hidden(X16,sK3(sK0,X17,k1_connsp_2(sK0,X17)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f189,f163])).

fof(f189,plain,(
    ! [X17,X16] :
      ( v4_pre_topc(X16,sK0)
      | ~ r2_hidden(X16,sK3(sK0,X17,k1_connsp_2(sK0,X17)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_connsp_2(sK0,X17),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f188,f77])).

fof(f188,plain,(
    ! [X17,X16] :
      ( v4_pre_topc(X16,sK0)
      | ~ r2_hidden(X16,sK3(sK0,X17,k1_connsp_2(sK0,X17)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_connsp_2(sK0,X17),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f78])).

fof(f154,plain,(
    ! [X17,X16] :
      ( v4_pre_topc(X16,sK0)
      | ~ r2_hidden(X16,sK3(sK0,X17,k1_connsp_2(sK0,X17)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_connsp_2(sK0,X17),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X17,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f76,f130])).

fof(f130,plain,(
    ! [X6,X0,X1] :
      ( v4_pre_topc(X6,X0)
      | ~ r2_hidden(X6,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f305,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | ~ v3_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f304,f76])).

fof(f304,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | ~ v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ v3_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f303,f77])).

fof(f303,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | ~ v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ v3_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f78])).

fof(f254,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,k1_xboole_0))
    | ~ v4_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ v3_pre_topc(sK4(sK0,sK1,k1_xboole_0),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK4(X0,X1,k1_xboole_0))
      | ~ v4_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | ~ v3_pre_topc(sK4(X0,X1,k1_xboole_0),X0)
      | ~ r2_hidden(sK4(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
