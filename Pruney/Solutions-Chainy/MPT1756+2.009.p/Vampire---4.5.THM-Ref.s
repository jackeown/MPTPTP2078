%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 528 expanded)
%              Number of leaves         :    4 (  90 expanded)
%              Depth                    :   39
%              Number of atoms          :  650 (7398 expanded)
%              Number of equality atoms :   10 ( 330 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(subsumption_resolution,[],[f348,f84])).

fof(f84,plain,(
    m1_connsp_2(sK4,sK1,sK5) ),
    inference(subsumption_resolution,[],[f82,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f42,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,
    ( ~ r1_tarski(sK4,sK4)
    | m1_connsp_2(sK4,sK1,sK5) ),
    inference(resolution,[],[f78,f21])).

fof(f21,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
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
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ( ( X5 = X6
                                    & r1_tarski(X4,u1_struct_0(X3))
                                    & r2_hidden(X5,X4)
                                    & v3_pre_topc(X4,X1) )
                                 => ( r1_tmap_1(X1,X0,X2,X5)
                                  <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(sK4,X0)
      | m1_connsp_2(X0,sK1,sK5) ) ),
    inference(subsumption_resolution,[],[f77,f17])).

fof(f17,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(sK4,X0)
      | ~ r2_hidden(sK5,sK4)
      | m1_connsp_2(X0,sK1,sK5) ) ),
    inference(subsumption_resolution,[],[f75,f21])).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(sK4,X0)
      | ~ r2_hidden(sK5,sK4)
      | m1_connsp_2(X0,sK1,sK5) ) ),
    inference(resolution,[],[f74,f16])).

fof(f16,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X1,X0)
      | ~ r2_hidden(sK5,X1)
      | m1_connsp_2(X0,sK1,sK5) ) ),
    inference(resolution,[],[f71,f20])).

fof(f20,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X2,sK1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f70,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X2,sK1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f28,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X2,sK1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(resolution,[],[f37,f29])).

% (2154)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f348,plain,(
    ~ m1_connsp_2(sK4,sK1,sK5) ),
    inference(subsumption_resolution,[],[f346,f18])).

fof(f18,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f346,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5) ),
    inference(resolution,[],[f345,f21])).

fof(f345,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5) ) ),
    inference(global_subsumption,[],[f46,f331,f344])).

fof(f344,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ) ),
    inference(subsumption_resolution,[],[f343,f45])).

fof(f45,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f15,f19])).

fof(f19,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f7])).

fof(f15,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f343,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ) ),
    inference(subsumption_resolution,[],[f342,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f342,plain,(
    ! [X0] :
      ( v2_struct_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ) ),
    inference(resolution,[],[f341,f23])).

fof(f23,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f341,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f340,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f340,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f339,f20])).

fof(f339,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f338,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f337,f25])).

fof(f25,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f336,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f336,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f335,f29])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f334,f28])).

fof(f334,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f333,f27])).

fof(f333,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f332,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f332,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f331,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X1,X0,sK2,X4)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tarski(X3,u1_struct_0(X2))
      | ~ m1_connsp_2(X3,X1,X4)
      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f43,f24])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f331,plain,(
    r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(subsumption_resolution,[],[f330,f18])).

fof(f330,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(subsumption_resolution,[],[f328,f84])).

fof(f328,plain,
    ( ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(resolution,[],[f327,f21])).

fof(f327,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(subsumption_resolution,[],[f326,f45])).

fof(f326,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(subsumption_resolution,[],[f325,f20])).

fof(f325,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(duplicate_literal_removal,[],[f324])).

% (2139)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f324,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(resolution,[],[f323,f47])).

fof(f47,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f13,f19])).

fof(f13,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f322,f22])).

fof(f322,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(resolution,[],[f294,f23])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f293,f26])).

fof(f293,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f292,f31])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f291,f30])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f290,f29])).

fof(f290,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f289,f28])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f288,f27])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f287,f32])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,sK1,X2)
      | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(resolution,[],[f175,f25])).

fof(f175,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_tarski(X3,u1_struct_0(X2))
      | ~ m1_connsp_2(X3,X1,X4)
      | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
      | r1_tmap_1(X1,X0,sK2,X4) ) ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f14,f19])).

fof(f14,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:28:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (2161)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (2153)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (2145)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (2147)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (2140)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (2161)Refutation not found, incomplete strategy% (2161)------------------------------
% 0.21/0.50  % (2161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (2161)Memory used [KB]: 10874
% 0.21/0.50  % (2161)Time elapsed: 0.065 s
% 0.21/0.50  % (2161)------------------------------
% 0.21/0.50  % (2161)------------------------------
% 0.21/0.50  % (2141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2143)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (2146)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (2144)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2148)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (2145)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f348,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    m1_connsp_2(sK4,sK1,sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f82,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f42,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~r1_tarski(sK4,sK4) | m1_connsp_2(sK4,sK1,sK5)),
% 0.21/0.51    inference(resolution,[],[f78,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK4,X0) | m1_connsp_2(X0,sK1,sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f77,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    r2_hidden(sK5,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK4,X0) | ~r2_hidden(sK5,sK4) | m1_connsp_2(X0,sK1,sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f21])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK4,X0) | ~r2_hidden(sK5,sK4) | m1_connsp_2(X0,sK1,sK5)) )),
% 0.21/0.52    inference(resolution,[],[f74,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    v3_pre_topc(sK4,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X1,X0) | ~r2_hidden(sK5,X1) | m1_connsp_2(X0,sK1,sK5)) )),
% 0.21/0.52    inference(resolution,[],[f71,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X2,sK1) | ~r1_tarski(X2,X1) | ~r2_hidden(X0,X2) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X2,sK1) | ~r1_tarski(X2,X1) | ~r2_hidden(X0,X2) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v2_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X2,sK1) | ~r1_tarski(X2,X1) | ~r2_hidden(X0,X2) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.52    inference(resolution,[],[f37,f29])).
% 0.21/0.52  % (2154)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    ~m1_connsp_2(sK4,sK1,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f346,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    ~r1_tarski(sK4,u1_struct_0(sK3)) | ~m1_connsp_2(sK4,sK1,sK5)),
% 0.21/0.52    inference(resolution,[],[f345,f21])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5)) )),
% 0.21/0.52    inference(global_subsumption,[],[f46,f331,f344])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f343,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.52    inference(forward_demodulation,[],[f15,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    sK5 = sK6),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f342,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ~v2_struct_0(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)) )),
% 0.21/0.52    inference(resolution,[],[f341,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f340,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f339,f20])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f338,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f337,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f336,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f335,f29])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f334,f28])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f333,f27])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f332,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f331,f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~r1_tmap_1(X1,X0,sK2,X4) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(resolution,[],[f43,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f330,f18])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    ~r1_tarski(sK4,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f328,f84])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ~m1_connsp_2(sK4,sK1,sK5) | ~r1_tarski(sK4,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(resolution,[],[f327,f21])).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X0,sK1,sK5) | ~r1_tarski(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f326,f45])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f325,f20])).
% 0.21/0.52  fof(f325,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f324])).
% 0.21/0.52  % (2139)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.21/0.52    inference(resolution,[],[f323,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(forward_demodulation,[],[f13,f19])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f323,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f322,f22])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,X1) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.21/0.52    inference(resolution,[],[f294,f23])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f293,f26])).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f292,f31])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f291,f30])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f290,f29])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f289,f28])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f288,f27])).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f287,f32])).
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.52    inference(resolution,[],[f175,f25])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) )),
% 0.21/0.52    inference(resolution,[],[f44,f24])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(forward_demodulation,[],[f14,f19])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2145)------------------------------
% 0.21/0.52  % (2145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2145)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2145)Memory used [KB]: 6524
% 0.21/0.52  % (2145)Time elapsed: 0.080 s
% 0.21/0.52  % (2145)------------------------------
% 0.21/0.52  % (2145)------------------------------
% 0.21/0.52  % (2138)Success in time 0.165 s
%------------------------------------------------------------------------------
