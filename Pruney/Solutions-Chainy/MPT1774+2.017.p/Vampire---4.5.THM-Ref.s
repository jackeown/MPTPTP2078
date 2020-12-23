%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:54 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 739 expanded)
%              Number of leaves         :    9 ( 140 expanded)
%              Depth                    :   45
%              Number of atoms          :  895 (9406 expanded)
%              Number of equality atoms :   17 ( 358 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(subsumption_resolution,[],[f266,f41])).

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

% (27515)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f266,plain,(
    v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f265,f249])).

fof(f249,plain,(
    r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(resolution,[],[f248,f65])).

% (27518)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f65,plain,
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

fof(f248,plain,(
    ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(subsumption_resolution,[],[f247,f64])).

fof(f64,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(forward_demodulation,[],[f25,f30])).

fof(f25,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f12])).

fof(f247,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(subsumption_resolution,[],[f246,f28])).

fof(f28,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f246,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(subsumption_resolution,[],[f245,f63])).

fof(f63,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f26,f30])).

fof(f26,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f245,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(resolution,[],[f244,f31])).

fof(f31,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f244,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK5)
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
      | r1_tmap_1(sK3,sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f243,f29])).

fof(f29,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f243,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
      | r1_tmap_1(sK3,sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f242,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f242,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
      | r1_tmap_1(sK3,sK0,sK4,X0) ) ),
    inference(resolution,[],[f241,f36])).

fof(f36,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1) ) ),
    inference(subsumption_resolution,[],[f240,f43])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(sK1)
      | ~ r2_hidden(X1,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1) ) ),
    inference(subsumption_resolution,[],[f239,f42])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(sK1)
      | ~ r2_hidden(X1,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1) ) ),
    inference(subsumption_resolution,[],[f238,f41])).

fof(f238,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(sK1)
      | ~ r2_hidden(X1,sK5)
      | ~ r1_tarski(sK5,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1) ) ),
    inference(resolution,[],[f237,f38])).

fof(f38,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f237,plain,(
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
      | r1_tmap_1(sK3,sK0,sK4,X2) ) ),
    inference(subsumption_resolution,[],[f236,f162])).

fof(f162,plain,(
    r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f159,f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f159,plain,(
    ! [X2] :
      ( r2_hidden(sK8(sK5,X2),u1_struct_0(sK3))
      | r1_tarski(sK5,X2) ) ),
    inference(resolution,[],[f157,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f56,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(sK3),X1)
      | r2_hidden(sK8(sK5,X0),X1)
      | r1_tarski(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f155,f69])).

fof(f69,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f66,f38])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK3)
      | r1_tarski(sK5,X0)
      | r2_hidden(sK8(sK5,X0),X1)
      | ~ r1_tarski(u1_struct_0(sK3),X1) ) ),
    inference(resolution,[],[f128,f36])).

fof(f128,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2)
      | r1_tarski(sK5,X1)
      | r2_hidden(sK8(sK5,X1),X3)
      | ~ r1_tarski(u1_struct_0(X2),X3) ) ),
    inference(resolution,[],[f123,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(sK5,X0),u1_struct_0(X1))
      | r1_tarski(sK5,X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK2,X1) ) ),
    inference(resolution,[],[f117,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f48,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(sK2),X1)
      | r2_hidden(sK8(sK5,X0),X1)
      | r1_tarski(sK5,X0) ) ),
    inference(resolution,[],[f115,f54])).

% (27517)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK5,X0),u1_struct_0(sK2))
      | r1_tarski(sK5,X0) ) ),
    inference(resolution,[],[f110,f77])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK5)
      | r2_hidden(sK8(X0,X1),u1_struct_0(sK2))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f101,f29])).

fof(f101,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK8(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f79,f54])).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK8(X1,X2),X3)
      | ~ r1_tarski(X1,X3)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f54,f55])).

fof(f236,plain,(
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
    inference(resolution,[],[f235,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f235,plain,(
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
    inference(resolution,[],[f234,f145])).

fof(f145,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(subsumption_resolution,[],[f144,f36])).

fof(f144,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f143,f69])).

fof(f143,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f138,f129])).

fof(f129,plain,(
    ! [X0] :
      ( r1_tarski(sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0] :
      ( r1_tarski(sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | r1_tarski(sK5,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f123,f56])).

fof(f138,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK3))
    | v3_pre_topc(sK5,sK3) ),
    inference(resolution,[],[f136,f38])).

% (27505)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | v3_pre_topc(sK5,X0)
      | ~ r1_tarski(sK5,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f134,f57])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK1)
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f133,f43])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f132,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK5,X0) ) ),
    inference(resolution,[],[f59,f27])).

fof(f27,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X2,X0,X3] :
      ( ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f234,plain,(
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
    inference(subsumption_resolution,[],[f233,f35])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f233,plain,(
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
    inference(subsumption_resolution,[],[f232,f37])).

% (27513)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f232,plain,(
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
    inference(subsumption_resolution,[],[f231,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f231,plain,(
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
    inference(subsumption_resolution,[],[f230,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f230,plain,(
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
    inference(subsumption_resolution,[],[f229,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f229,plain,(
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
    inference(resolution,[],[f228,f34])).

fof(f34,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

% (27507)Refutation not found, incomplete strategy% (27507)------------------------------
% (27507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27507)Termination reason: Refutation not found, incomplete strategy

% (27507)Memory used [KB]: 10874
% (27507)Time elapsed: 0.118 s
% (27507)------------------------------
% (27507)------------------------------
fof(f228,plain,(
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
    inference(subsumption_resolution,[],[f227,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f227,plain,(
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
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
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
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f265,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f264,f36])).

fof(f264,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f263,f63])).

fof(f263,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f262,f31])).

fof(f262,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f261,f35])).

fof(f261,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f260,f34])).

fof(f260,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f259,f33])).

fof(f259,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f258,f40])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f258,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f257,f39])).

fof(f257,plain,
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
    inference(subsumption_resolution,[],[f256,f38])).

fof(f256,plain,
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
    inference(subsumption_resolution,[],[f255,f37])).

fof(f255,plain,
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
    inference(subsumption_resolution,[],[f254,f46])).

fof(f254,plain,
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
    inference(subsumption_resolution,[],[f253,f45])).

fof(f253,plain,
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
    inference(subsumption_resolution,[],[f252,f44])).

fof(f252,plain,
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
    inference(subsumption_resolution,[],[f251,f43])).

fof(f251,plain,
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
    inference(subsumption_resolution,[],[f250,f42])).

fof(f250,plain,
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
    inference(resolution,[],[f248,f62])).

fof(f62,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.51  % (27527)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.51  % (27519)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.51  % (27511)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.51  % (27508)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.52  % (27509)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.52  % (27510)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (27507)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (27527)Refutation not found, incomplete strategy% (27527)------------------------------
% 0.23/0.52  % (27527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (27527)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (27527)Memory used [KB]: 11001
% 0.23/0.53  % (27527)Time elapsed: 0.055 s
% 0.23/0.53  % (27527)------------------------------
% 0.23/0.53  % (27527)------------------------------
% 0.23/0.53  % (27512)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.53  % (27526)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.53  % (27525)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.53  % (27533)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.53  % (27511)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f267,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f266,f41])).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ~v2_struct_0(sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.53    inference(flattening,[],[f11])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,negated_conjecture,(
% 0.23/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.23/0.54    inference(negated_conjecture,[],[f9])).
% 0.23/0.54  % (27515)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.54  fof(f9,conjecture,(
% 0.23/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.23/0.54  fof(f266,plain,(
% 0.23/0.54    v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f265,f249])).
% 0.23/0.54  fof(f249,plain,(
% 0.23/0.54    r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.23/0.54    inference(resolution,[],[f248,f65])).
% 0.23/0.54  % (27518)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.54  fof(f65,plain,(
% 0.23/0.54    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.23/0.54    inference(forward_demodulation,[],[f24,f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    sK6 = sK7),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f248,plain,(
% 0.23/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.23/0.54    inference(subsumption_resolution,[],[f247,f64])).
% 0.23/0.54  fof(f64,plain,(
% 0.23/0.54    ~r1_tmap_1(sK3,sK0,sK4,sK6) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.23/0.54    inference(forward_demodulation,[],[f25,f30])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f247,plain,(
% 0.23/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.23/0.54    inference(subsumption_resolution,[],[f246,f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    r2_hidden(sK6,sK5)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f246,plain,(
% 0.23/0.54    ~r2_hidden(sK6,sK5) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.23/0.54    inference(subsumption_resolution,[],[f245,f63])).
% 0.23/0.54  fof(f63,plain,(
% 0.23/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.23/0.54    inference(forward_demodulation,[],[f26,f30])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f245,plain,(
% 0.23/0.54    ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.23/0.54    inference(resolution,[],[f244,f31])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f244,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK5) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | r1_tmap_1(sK3,sK0,sK4,X0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f243,f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f243,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | r1_tmap_1(sK3,sK0,sK4,X0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f242,f39])).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ~v2_struct_0(sK2)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f242,plain,(
% 0.23/0.54    ( ! [X0] : (v2_struct_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | r1_tmap_1(sK3,sK0,sK4,X0)) )),
% 0.23/0.54    inference(resolution,[],[f241,f36])).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    m1_pre_topc(sK2,sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f241,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f240,f43])).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    l1_pre_topc(sK1)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f240,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~r2_hidden(X1,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f239,f42])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    v2_pre_topc(sK1)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f239,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~r2_hidden(X1,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f238,f41])).
% 0.23/0.54  fof(f238,plain,(
% 0.23/0.54    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~r2_hidden(X1,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1)) )),
% 0.23/0.54    inference(resolution,[],[f237,f38])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    m1_pre_topc(sK3,sK1)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f237,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r2_hidden(X2,sK5) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK0,sK4,X2)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f236,f162])).
% 0.23/0.54  fof(f162,plain,(
% 0.23/0.54    r1_tarski(sK5,u1_struct_0(sK3))),
% 0.23/0.54    inference(duplicate_literal_removal,[],[f160])).
% 0.23/0.54  fof(f160,plain,(
% 0.23/0.54    r1_tarski(sK5,u1_struct_0(sK3)) | r1_tarski(sK5,u1_struct_0(sK3))),
% 0.23/0.54    inference(resolution,[],[f159,f56])).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f23])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.54  fof(f159,plain,(
% 0.23/0.54    ( ! [X2] : (r2_hidden(sK8(sK5,X2),u1_struct_0(sK3)) | r1_tarski(sK5,X2)) )),
% 0.23/0.54    inference(resolution,[],[f157,f77])).
% 0.23/0.54  fof(f77,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.23/0.54    inference(duplicate_literal_removal,[],[f76])).
% 0.23/0.54  fof(f76,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.23/0.54    inference(resolution,[],[f56,f55])).
% 0.23/0.54  fof(f55,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f23])).
% 0.23/0.54  fof(f157,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK3),X1) | r2_hidden(sK8(sK5,X0),X1) | r1_tarski(sK5,X0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f155,f69])).
% 0.23/0.54  fof(f69,plain,(
% 0.23/0.54    l1_pre_topc(sK3)),
% 0.23/0.54    inference(resolution,[],[f66,f38])).
% 0.23/0.54  fof(f66,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)) )),
% 0.23/0.54    inference(resolution,[],[f47,f43])).
% 0.23/0.54  fof(f47,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f13])).
% 0.23/0.54  fof(f13,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.23/0.54  fof(f155,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~l1_pre_topc(sK3) | r1_tarski(sK5,X0) | r2_hidden(sK8(sK5,X0),X1) | ~r1_tarski(u1_struct_0(sK3),X1)) )),
% 0.23/0.54    inference(resolution,[],[f128,f36])).
% 0.23/0.54  fof(f128,plain,(
% 0.23/0.54    ( ! [X2,X3,X1] : (~m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2) | r1_tarski(sK5,X1) | r2_hidden(sK8(sK5,X1),X3) | ~r1_tarski(u1_struct_0(X2),X3)) )),
% 0.23/0.54    inference(resolution,[],[f123,f54])).
% 0.23/0.54  fof(f54,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f23])).
% 0.23/0.54  fof(f123,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r2_hidden(sK8(sK5,X0),u1_struct_0(X1)) | r1_tarski(sK5,X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2,X1)) )),
% 0.23/0.54    inference(resolution,[],[f117,f88])).
% 0.23/0.54  fof(f88,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.23/0.54    inference(resolution,[],[f48,f58])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.54  fof(f48,plain,(
% 0.23/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.23/0.54  fof(f117,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK2),X1) | r2_hidden(sK8(sK5,X0),X1) | r1_tarski(sK5,X0)) )),
% 0.23/0.54    inference(resolution,[],[f115,f54])).
% 0.23/0.54  % (27517)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  fof(f115,plain,(
% 0.23/0.54    ( ! [X0] : (r2_hidden(sK8(sK5,X0),u1_struct_0(sK2)) | r1_tarski(sK5,X0)) )),
% 0.23/0.54    inference(resolution,[],[f110,f77])).
% 0.23/0.54  fof(f110,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(X0,sK5) | r2_hidden(sK8(X0,X1),u1_struct_0(sK2)) | r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(resolution,[],[f101,f29])).
% 0.23/0.54  fof(f101,plain,(
% 0.23/0.54    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK8(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 0.23/0.54    inference(resolution,[],[f79,f54])).
% 0.23/0.54  fof(f79,plain,(
% 0.23/0.54    ( ! [X2,X3,X1] : (r2_hidden(sK8(X1,X2),X3) | ~r1_tarski(X1,X3) | r1_tarski(X1,X2)) )),
% 0.23/0.54    inference(resolution,[],[f54,f55])).
% 0.23/0.54  fof(f236,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r2_hidden(X2,sK5) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK0,sK4,X2) | ~r1_tarski(sK5,u1_struct_0(sK3))) )),
% 0.23/0.54    inference(resolution,[],[f235,f57])).
% 0.23/0.54  fof(f57,plain,(
% 0.23/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f2])).
% 0.23/0.54  fof(f235,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~r2_hidden(X2,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) | r1_tmap_1(sK3,sK0,sK4,X2)) )),
% 0.23/0.54    inference(resolution,[],[f234,f145])).
% 0.23/0.54  fof(f145,plain,(
% 0.23/0.54    v3_pre_topc(sK5,sK3)),
% 0.23/0.54    inference(subsumption_resolution,[],[f144,f36])).
% 0.23/0.54  fof(f144,plain,(
% 0.23/0.54    v3_pre_topc(sK5,sK3) | ~m1_pre_topc(sK2,sK3)),
% 0.23/0.54    inference(subsumption_resolution,[],[f143,f69])).
% 0.23/0.54  fof(f143,plain,(
% 0.23/0.54    v3_pre_topc(sK5,sK3) | ~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3)),
% 0.23/0.54    inference(resolution,[],[f138,f129])).
% 0.23/0.54  fof(f129,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(sK5,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0)) )),
% 0.23/0.54    inference(duplicate_literal_removal,[],[f127])).
% 0.23/0.54  fof(f127,plain,(
% 0.23/0.54    ( ! [X0] : (r1_tarski(sK5,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | r1_tarski(sK5,u1_struct_0(X0))) )),
% 0.23/0.54    inference(resolution,[],[f123,f56])).
% 0.23/0.54  fof(f138,plain,(
% 0.23/0.54    ~r1_tarski(sK5,u1_struct_0(sK3)) | v3_pre_topc(sK5,sK3)),
% 0.23/0.54    inference(resolution,[],[f136,f38])).
% 0.23/0.54  % (27505)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  fof(f136,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v3_pre_topc(sK5,X0) | ~r1_tarski(sK5,u1_struct_0(X0))) )),
% 0.23/0.54    inference(resolution,[],[f134,f57])).
% 0.23/0.54  fof(f134,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | v3_pre_topc(sK5,X0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f133,f43])).
% 0.23/0.54  fof(f133,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5,X0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f132,f32])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f132,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5,X0)) )),
% 0.23/0.54    inference(resolution,[],[f59,f27])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    v3_pre_topc(sK5,sK1)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f59,plain,(
% 0.23/0.54    ( ! [X2,X0,X3] : (~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 0.23/0.54    inference(equality_resolution,[],[f49])).
% 0.23/0.54  fof(f49,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.54    inference(flattening,[],[f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.23/0.54  fof(f234,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(X2,sK3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f233,f35])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f233,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f232,f37])).
% 0.23/0.54  % (27513)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ~v2_struct_0(sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f232,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f231,f46])).
% 0.23/0.54  fof(f46,plain,(
% 0.23/0.54    l1_pre_topc(sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f231,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f230,f45])).
% 0.23/0.54  fof(f45,plain,(
% 0.23/0.54    v2_pre_topc(sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f230,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f229,f44])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    ~v2_struct_0(sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f229,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X3) | r1_tmap_1(sK3,sK0,sK4,X3)) )),
% 0.23/0.54    inference(resolution,[],[f228,f34])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  % (27507)Refutation not found, incomplete strategy% (27507)------------------------------
% 0.23/0.54  % (27507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (27507)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (27507)Memory used [KB]: 10874
% 0.23/0.54  % (27507)Time elapsed: 0.118 s
% 0.23/0.54  % (27507)------------------------------
% 0.23/0.54  % (27507)------------------------------
% 0.23/0.54  fof(f228,plain,(
% 0.23/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~v3_pre_topc(X4,X3) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X5) | r1_tmap_1(X3,X1,sK4,X5)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f227,f53])).
% 0.23/0.54  fof(f53,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.54    inference(flattening,[],[f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.23/0.54  fof(f227,plain,(
% 0.23/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~v3_pre_topc(X4,X3) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X5) | r1_tmap_1(X3,X1,sK4,X5)) )),
% 0.23/0.54    inference(resolution,[],[f61,f33])).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    v1_funct_1(sK4)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f61,plain,(
% 0.23/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X7,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.23/0.54    inference(equality_resolution,[],[f50])).
% 0.23/0.54  fof(f50,plain,(
% 0.23/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X6,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.54    inference(flattening,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.23/0.54  fof(f265,plain,(
% 0.23/0.54    ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f264,f36])).
% 0.23/0.54  fof(f264,plain,(
% 0.23/0.54    ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f263,f63])).
% 0.23/0.54  fof(f263,plain,(
% 0.23/0.54    ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f262,f31])).
% 0.23/0.54  fof(f262,plain,(
% 0.23/0.54    ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f261,f35])).
% 0.23/0.54  fof(f261,plain,(
% 0.23/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f260,f34])).
% 0.23/0.54  fof(f260,plain,(
% 0.23/0.54    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f259,f33])).
% 0.23/0.54  fof(f259,plain,(
% 0.23/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f258,f40])).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    m1_pre_topc(sK2,sK1)),
% 0.23/0.54    inference(cnf_transformation,[],[f12])).
% 0.23/0.54  fof(f258,plain,(
% 0.23/0.54    ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f257,f39])).
% 0.23/0.54  fof(f257,plain,(
% 0.23/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f256,f38])).
% 0.23/0.54  fof(f256,plain,(
% 0.23/0.54    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f255,f37])).
% 0.23/0.54  fof(f255,plain,(
% 0.23/0.54    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f254,f46])).
% 0.23/0.54  fof(f254,plain,(
% 0.23/0.54    ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f253,f45])).
% 0.23/0.54  fof(f253,plain,(
% 0.23/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f252,f44])).
% 0.23/0.54  fof(f252,plain,(
% 0.23/0.54    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f251,f43])).
% 0.23/0.54  fof(f251,plain,(
% 0.23/0.54    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f250,f42])).
% 0.23/0.54  fof(f250,plain,(
% 0.23/0.54    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)),
% 0.23/0.54    inference(resolution,[],[f248,f62])).
% 1.37/0.54  fof(f62,plain,(
% 1.37/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X6) | v2_struct_0(X0)) )),
% 1.37/0.54    inference(equality_resolution,[],[f52])).
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f20])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f19])).
% 1.37/0.54  fof(f19,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (27511)------------------------------
% 1.37/0.54  % (27511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (27511)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (27511)Memory used [KB]: 6524
% 1.37/0.54  % (27511)Time elapsed: 0.083 s
% 1.37/0.54  % (27511)------------------------------
% 1.37/0.54  % (27511)------------------------------
% 1.37/0.55  % (27502)Success in time 0.177 s
%------------------------------------------------------------------------------
