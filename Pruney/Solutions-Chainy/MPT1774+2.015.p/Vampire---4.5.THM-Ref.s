%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 765 expanded)
%              Number of leaves         :    9 ( 140 expanded)
%              Depth                    :   49
%              Number of atoms          :  956 (10460 expanded)
%              Number of equality atoms :   19 ( 410 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(subsumption_resolution,[],[f254,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f254,plain,(
    v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f253,f227])).

fof(f227,plain,(
    r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(subsumption_resolution,[],[f226,f42])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f226,plain,
    ( ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(subsumption_resolution,[],[f225,f43])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(subsumption_resolution,[],[f224,f41])).

fof(f224,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(subsumption_resolution,[],[f223,f38])).

fof(f38,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f223,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(resolution,[],[f217,f72])).

fof(f72,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f24,f30])).

fof(f30,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f12])).

fof(f217,plain,(
    ! [X1] :
      ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(subsumption_resolution,[],[f216,f29])).

fof(f29,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f216,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(sK5,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(subsumption_resolution,[],[f215,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f215,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(sK5,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(subsumption_resolution,[],[f211,f36])).

fof(f36,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f211,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(sK2,sK3)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(sK5,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(resolution,[],[f209,f70])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f26,f30])).

fof(f26,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6,u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(sK5,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(subsumption_resolution,[],[f208,f28])).

fof(f28,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f208,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_subset_1(sK6,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(sK6,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(resolution,[],[f207,f31])).

fof(f31,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK3))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
      | r1_tmap_1(sK3,sK0,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f206,f131])).

fof(f131,plain,(
    r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f127,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK5,X0),u1_struct_0(sK3))
      | r1_tarski(sK5,X0) ) ),
    inference(resolution,[],[f109,f121])).

fof(f121,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f120,f36])).

fof(f120,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f117,f38])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f73,f43])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(sK2),X1)
      | r2_hidden(sK8(sK5,X0),X1)
      | r1_tarski(sK5,X0) ) ),
    inference(resolution,[],[f107,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK5,X0),u1_struct_0(sK2))
      | r1_tarski(sK5,X0) ) ),
    inference(resolution,[],[f104,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f104,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,sK5)
      | r2_hidden(sK8(X3,X4),u1_struct_0(sK2))
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f94,f29])).

fof(f94,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK8(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f84,f58])).

fof(f84,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK8(X1,X2),X3)
      | ~ r1_tarski(X1,X3)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
      | r1_tmap_1(sK3,sK0,sK4,X2)
      | ~ r1_tarski(sK5,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f205,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X2,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2)
      | r1_tmap_1(sK3,sK0,sK4,X2) ) ),
    inference(resolution,[],[f204,f177])).

fof(f177,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(subsumption_resolution,[],[f175,f131])).

fof(f175,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f173,f38])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | v3_pre_topc(sK5,X0)
      | ~ r1_tarski(sK5,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f171,f61])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK1)
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f170,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | ~ r1_tarski(sK5,sK5)
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f168,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | ~ r1_tarski(sK5,sK5)
      | v3_pre_topc(sK5,X0) ) ),
    inference(resolution,[],[f167,f27])).

fof(f27,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ r1_tarski(sK5,X1)
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f166,f42])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ r1_tarski(sK5,X1)
      | ~ v2_pre_topc(sK1)
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f165,f32])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ r1_tarski(sK5,X1)
      | ~ v2_pre_topc(sK1)
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f164,f43])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ r1_tarski(sK5,X1)
      | ~ v2_pre_topc(sK1)
      | v3_pre_topc(sK5,X0) ) ),
    inference(resolution,[],[f67,f27])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v3_pre_topc(X4,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tarski(X4,X2)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X4,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tarski(X3,X2)
      | X3 != X4
      | ~ v3_pre_topc(X3,X0)
      | v3_pre_topc(X4,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( X3 = X4
                          & r1_tarski(X3,X2)
                          & r1_tarski(X2,u1_struct_0(X1))
                          & v3_pre_topc(X2,X0) )
                       => ( v3_pre_topc(X4,X1)
                        <=> v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).

fof(f204,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_pre_topc(X2,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3)
      | r1_tmap_1(sK3,sK0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f203,f35])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f203,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,sK3)
      | ~ r2_hidden(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3)
      | r1_tmap_1(sK3,sK0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f202,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f202,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,sK3)
      | ~ r2_hidden(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3)
      | r1_tmap_1(sK3,sK0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f201,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f201,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,sK3)
      | ~ r2_hidden(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3)
      | r1_tmap_1(sK3,sK0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f200,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f200,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,sK3)
      | ~ r2_hidden(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3)
      | r1_tmap_1(sK3,sK0,sK4,X3) ) ),
    inference(subsumption_resolution,[],[f199,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f199,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,sK3)
      | ~ r2_hidden(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3)
      | r1_tmap_1(sK3,sK0,sK4,X3) ) ),
    inference(resolution,[],[f198,f34])).

fof(f34,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f198,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ v3_pre_topc(X4,X3)
      | ~ r2_hidden(X5,X4)
      | ~ r1_tarski(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X5)
      | r1_tmap_1(X3,X1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f197,f50])).

fof(f197,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ v3_pre_topc(X4,X3)
      | ~ r2_hidden(X5,X4)
      | ~ r1_tarski(X4,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X5)
      | r1_tmap_1(X3,X1,sK4,X5) ) ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X7,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X6,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

% (22756)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f253,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f252,f36])).

fof(f252,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f251,f70])).

fof(f251,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f250,f31])).

fof(f250,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f249,f35])).

fof(f249,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f248,f34])).

fof(f248,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f247,f33])).

fof(f247,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f246,f40])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f246,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f245,f39])).

fof(f245,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f244,f38])).

fof(f244,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f243,f37])).

fof(f243,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f242,f46])).

fof(f242,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f241,f45])).

fof(f241,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f240,f44])).

fof(f240,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f239,f43])).

fof(f239,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f238,f42])).

fof(f238,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f228,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f228,plain,(
    ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(resolution,[],[f227,f71])).

fof(f71,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(forward_demodulation,[],[f25,f30])).

fof(f25,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (22743)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22765)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (22759)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (22745)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (22746)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (22749)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (22751)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (22742)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (22768)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (22741)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (22760)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (22739)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (22766)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (22740)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (22747)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (22752)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (22757)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (22744)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (22758)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (22745)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f254,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f253,f227])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f226,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v2_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    ~v2_pre_topc(sK1) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f225,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    l1_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f224,f41])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f223,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f220])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | r1_tmap_1(sK3,sK0,sK4,sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(resolution,[],[f217,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(forward_demodulation,[],[f24,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    sK6 = sK7),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f216,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ( ! [X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f215,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ~v2_struct_0(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    ( ! [X1] : (~v2_pre_topc(X1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f211,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    m1_pre_topc(sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    ( ! [X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.54    inference(resolution,[],[f209,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.54    inference(forward_demodulation,[],[f26,f30])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(sK6,u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f208,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    r2_hidden(sK6,sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.21/0.54    inference(resolution,[],[f207,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK3)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r2_hidden(X2,sK5) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK0,sK4,X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f206,f131])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    r1_tarski(sK5,u1_struct_0(sK3))),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    r1_tarski(sK5,u1_struct_0(sK3)) | r1_tarski(sK5,u1_struct_0(sK3))),
% 0.21/0.54    inference(resolution,[],[f127,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK8(sK5,X0),u1_struct_0(sK3)) | r1_tarski(sK5,X0)) )),
% 0.21/0.54    inference(resolution,[],[f109,f121])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.54    inference(resolution,[],[f120,f36])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK3) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK3))) )),
% 0.21/0.54    inference(resolution,[],[f117,f38])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f42])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.54    inference(resolution,[],[f73,f43])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f51,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK2),X1) | r2_hidden(sK8(sK5,X0),X1) | r1_tarski(sK5,X0)) )),
% 0.21/0.54    inference(resolution,[],[f107,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK8(sK5,X0),u1_struct_0(sK2)) | r1_tarski(sK5,X0)) )),
% 0.21/0.54    inference(resolution,[],[f104,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r1_tarski(X3,sK5) | r2_hidden(sK8(X3,X4),u1_struct_0(sK2)) | r1_tarski(X3,X4)) )),
% 0.21/0.54    inference(resolution,[],[f94,f29])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK8(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 0.21/0.54    inference(resolution,[],[f84,f58])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (r2_hidden(sK8(X1,X2),X3) | ~r1_tarski(X1,X3) | r1_tarski(X1,X2)) )),
% 0.21/0.54    inference(resolution,[],[f58,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r2_hidden(X2,sK5) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK0,sK4,X2) | ~r1_tarski(sK5,u1_struct_0(sK3))) )),
% 0.21/0.54    inference(resolution,[],[f205,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~r2_hidden(X2,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) | r1_tmap_1(sK3,sK0,sK4,X2)) )),
% 0.21/0.54    inference(resolution,[],[f204,f177])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    v3_pre_topc(sK5,sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f175,f131])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    v3_pre_topc(sK5,sK3) | ~r1_tarski(sK5,u1_struct_0(sK3))),
% 0.21/0.54    inference(resolution,[],[f173,f38])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v3_pre_topc(sK5,X0) | ~r1_tarski(sK5,u1_struct_0(X0))) )),
% 0.21/0.54    inference(resolution,[],[f171,f61])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f170,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(sK5,u1_struct_0(X0)) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f169,f68])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tarski(sK5,sK5) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f168,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tarski(sK5,sK5) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(resolution,[],[f167,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    v3_pre_topc(sK5,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tarski(sK5,X1) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f166,f42])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,sK1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tarski(sK5,X1) | ~v2_pre_topc(sK1) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f165,f32])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,sK1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tarski(sK5,X1) | ~v2_pre_topc(sK1) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f164,f43])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,sK1) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tarski(sK5,X1) | ~v2_pre_topc(sK1) | v3_pre_topc(sK5,X0)) )),
% 0.21/0.54    inference(resolution,[],[f67,f27])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~v3_pre_topc(X4,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tarski(X4,X2) | ~v2_pre_topc(X0) | v3_pre_topc(X4,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tarski(X3,X2) | X3 != X4 | ~v3_pre_topc(X3,X0) | v3_pre_topc(X4,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | (X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ((X3 = X4 & r1_tarski(X3,X2) & r1_tarski(X2,u1_struct_0(X1)) & v3_pre_topc(X2,X0)) => (v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(X2,sK3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f203,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f202,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ~v2_struct_0(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f201,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f200,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f199,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.21/0.54    inference(resolution,[],[f198,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~v3_pre_topc(X4,X3) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X5) | r1_tmap_1(X3,X1,sK4,X5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f197,f50])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~v3_pre_topc(X4,X3) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X5) | r1_tmap_1(X3,X1,sK4,X5)) )),
% 0.21/0.54    inference(resolution,[],[f64,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X7,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.21/0.54    inference(equality_resolution,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X6,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  % (22756)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f252,f36])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f251,f70])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f250,f31])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f249,f35])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f248,f34])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f247,f33])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f246,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    m1_pre_topc(sK2,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f245,f39])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f244,f38])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f243,f37])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f242,f46])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f241,f45])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f240,f44])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f239,f43])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f238,f42])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.21/0.54    inference(resolution,[],[f228,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X6) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.21/0.54    inference(resolution,[],[f227,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~r1_tmap_1(sK3,sK0,sK4,sK6) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.21/0.54    inference(forward_demodulation,[],[f25,f30])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (22745)------------------------------
% 0.21/0.54  % (22745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22745)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (22745)Memory used [KB]: 6524
% 0.21/0.54  % (22745)Time elapsed: 0.124 s
% 0.21/0.54  % (22745)------------------------------
% 0.21/0.54  % (22745)------------------------------
% 0.21/0.55  % (22750)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22761)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (22762)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (22753)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (22754)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (22764)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (22765)Refutation not found, incomplete strategy% (22765)------------------------------
% 0.21/0.55  % (22765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22755)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.56  % (22741)Refutation not found, incomplete strategy% (22741)------------------------------
% 1.38/0.56  % (22741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (22741)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (22741)Memory used [KB]: 10874
% 1.38/0.56  % (22741)Time elapsed: 0.144 s
% 1.38/0.56  % (22741)------------------------------
% 1.38/0.56  % (22741)------------------------------
% 1.38/0.56  % (22765)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (22765)Memory used [KB]: 10874
% 1.38/0.56  % (22765)Time elapsed: 0.132 s
% 1.38/0.56  % (22765)------------------------------
% 1.38/0.56  % (22765)------------------------------
% 1.38/0.56  % (22738)Success in time 0.202 s
%------------------------------------------------------------------------------
