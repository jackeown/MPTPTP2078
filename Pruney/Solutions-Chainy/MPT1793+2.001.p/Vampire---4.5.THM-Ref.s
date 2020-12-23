%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 656 expanded)
%              Number of leaves         :   26 ( 275 expanded)
%              Depth                    :   18
%              Number of atoms          :  769 (5182 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f174,f186,f196,f207,f237])).

fof(f237,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f235,f108])).

fof(f108,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_4
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f235,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f234,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & r1_xboole_0(u1_struct_0(sK2),sK1)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),X1)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),sK1)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
            & m1_subset_1(X3,u1_struct_0(X2)) )
        & r1_xboole_0(u1_struct_0(X2),sK1)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & r1_xboole_0(u1_struct_0(sK2),sK1)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f234,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f233,f119])).

fof(f119,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f118,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,
    ( v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f117,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f71,f61])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f233,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f230,f90])).

fof(f90,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f89,f58])).

fof(f89,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f61])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f230,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f151,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f151,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(X9)) ) ),
    inference(subsumption_resolution,[],[f145,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(k1_connsp_2(X1,X0)) ) ),
    inference(resolution,[],[f68,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f145,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | v1_xboole_0(k1_connsp_2(X9,X8))
      | ~ v1_xboole_0(u1_struct_0(X9)) ) ),
    inference(resolution,[],[f78,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f207,plain,
    ( ~ spl6_3
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f205,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f204,f58])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f203,f61])).

fof(f203,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_9 ),
    inference(resolution,[],[f202,f140])).

fof(f140,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f139,f60])).

fof(f139,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f67,f63])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f202,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f201,f56])).

fof(f201,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f200,f57])).

fof(f200,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f199,f58])).

fof(f199,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f198,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f198,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f197,f176])).

fof(f176,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f120,f105])).

fof(f105,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_3
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f76,f62])).

fof(f62,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f197,plain,
    ( r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_9 ),
    inference(resolution,[],[f173,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

fof(f173,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_9
  <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f196,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f194,f56])).

fof(f194,plain,
    ( v2_struct_0(sK0)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f193,f57])).

fof(f193,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f192,f58])).

fof(f192,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f191,f59])).

fof(f191,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(resolution,[],[f170,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f170,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_8
  <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f186,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f184,f56])).

fof(f184,plain,
    ( v2_struct_0(sK0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f183,f57])).

fof(f183,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f182,f58])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f181,f59])).

fof(f181,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7 ),
    inference(resolution,[],[f167,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f167,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_7
  <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f174,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f164,f172,f169,f166])).

fof(f164,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f163,f126])).

fof(f126,plain,(
    ~ v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f125,f56])).

fof(f125,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f124,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f58])).

fof(f123,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f163,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f162,f130])).

fof(f130,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f129,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f128,f57])).

fof(f128,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f58])).

fof(f127,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f80,f59])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f162,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f161,f138])).

fof(f138,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f137,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f57])).

fof(f136,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f58])).

fof(f135,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f59])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

% (21712)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f161,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f160,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f159,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f158,f58])).

fof(f158,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f157,f134])).

fof(f134,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f133,f56])).

fof(f133,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f57])).

fof(f132,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f58])).

fof(f131,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f81,f59])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f157,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f156,f60])).

fof(f156,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f155,f61])).

fof(f155,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f154,f63])).

fof(f154,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f87,f64])).

fof(f64,plain,(
    ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f67])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f109,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f101,f107,f104])).

fof(f101,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f77,f63])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (21717)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (21709)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (21717)Refutation not found, incomplete strategy% (21717)------------------------------
% 0.21/0.48  % (21717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21717)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21717)Memory used [KB]: 6140
% 0.21/0.48  % (21717)Time elapsed: 0.061 s
% 0.21/0.48  % (21717)------------------------------
% 0.21/0.48  % (21717)------------------------------
% 0.21/0.48  % (21714)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (21709)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f109,f174,f186,f196,f207,f237])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ~spl6_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    $false | ~spl6_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f235,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK2)) | ~spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl6_4 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    (((~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f48,f47,f46,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    v2_struct_0(sK2) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f233,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    v2_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    v2_pre_topc(sK2) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    v2_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f71,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    m1_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    l1_pre_topc(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f58])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f66,f61])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.48    inference(resolution,[],[f151,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~m1_subset_1(X8,u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | ~v1_xboole_0(u1_struct_0(X9))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f145,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(k1_connsp_2(X1,X0))) )),
% 0.21/0.48    inference(resolution,[],[f68,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(rectify,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~m1_subset_1(X8,u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | v1_xboole_0(k1_connsp_2(X9,X8)) | ~v1_xboole_0(u1_struct_0(X9))) )),
% 0.21/0.48    inference(resolution,[],[f78,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ~spl6_3 | spl6_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    $false | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f205,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f204,f58])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f61])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(resolution,[],[f202,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f139,f60])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f67,f63])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f56])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f200,f57])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f199,f58])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f198,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f197,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK1) | ~spl6_3),
% 0.21/0.48    inference(resolution,[],[f120,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl6_3 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.48    inference(resolution,[],[f76,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    r1_xboole_0(u1_struct_0(sK2),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    r2_hidden(sK3,sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_9),
% 0.21/0.48    inference(resolution,[],[f173,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl6_9 <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    spl6_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    $false | spl6_8),
% 0.21/0.48    inference(subsumption_resolution,[],[f194,f56])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    v2_struct_0(sK0) | spl6_8),
% 0.21/0.48    inference(subsumption_resolution,[],[f193,f57])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_8),
% 0.21/0.48    inference(subsumption_resolution,[],[f192,f58])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_8),
% 0.21/0.48    inference(subsumption_resolution,[],[f191,f59])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_8),
% 0.21/0.48    inference(resolution,[],[f170,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f169])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl6_8 <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl6_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f185])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    $false | spl6_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f184,f56])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    v2_struct_0(sK0) | spl6_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f183,f57])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f182,f58])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f59])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_7),
% 0.21/0.48    inference(resolution,[],[f167,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl6_7 <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f164,f172,f169,f166])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f163,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f56])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f57])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f58])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~v2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f79,f59])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f162,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f56])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f57])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f58])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f80,f59])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f161,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f56])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    l1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f57])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f58])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f85,f59])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f43])).
% 0.21/0.48  % (21712)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f160,f56])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f159,f57])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f58])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f157,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    v1_funct_1(k7_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f56])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    v1_funct_1(k7_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f57])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f131,f58])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f81,f59])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f60])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | v2_struct_0(sK2) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f155,f61])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f154,f63])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f87,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f67])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl6_3 | spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f101,f107,f104])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.49    inference(resolution,[],[f77,f63])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (21709)------------------------------
% 0.21/0.49  % (21709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21709)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (21709)Memory used [KB]: 10746
% 0.21/0.49  % (21709)Time elapsed: 0.064 s
% 0.21/0.49  % (21709)------------------------------
% 0.21/0.49  % (21709)------------------------------
% 0.21/0.49  % (21706)Success in time 0.128 s
%------------------------------------------------------------------------------
