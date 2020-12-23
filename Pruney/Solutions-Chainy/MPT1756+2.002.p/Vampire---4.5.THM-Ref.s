%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 502 expanded)
%              Number of leaves         :    7 (  87 expanded)
%              Depth                    :   36
%              Number of atoms          :  657 (6789 expanded)
%              Number of equality atoms :   15 ( 314 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(global_subsumption,[],[f58,f126,f139])).

fof(f139,plain,(
    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f138,f57])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f22,f26])).

fof(f26,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

% (13947)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f22,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f138,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(subsumption_resolution,[],[f137,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f137,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(resolution,[],[f136,f30])).

fof(f30,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f135,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f134,f27])).

fof(f27,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f134,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f133,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f132,f32])).

fof(f32,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f131,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f131,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f130,f36])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f130,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f129,f35])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f128,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f128,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f127,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f127,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) ) ),
    inference(resolution,[],[f126,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X1,X0,sK2,X3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ v2_pre_topc(X0)
      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X3) ) ),
    inference(resolution,[],[f52,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
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
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
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
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f126,plain,(
    r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(subsumption_resolution,[],[f125,f28])).

fof(f28,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f125,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(subsumption_resolution,[],[f124,f25])).

fof(f25,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f124,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(resolution,[],[f123,f102])).

fof(f102,plain,(
    m1_connsp_2(sK4,sK1,sK5) ),
    inference(subsumption_resolution,[],[f101,f90])).

fof(f90,plain,(
    r2_hidden(sK5,k1_tops_1(sK1,sK4)) ),
    inference(resolution,[],[f87,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK1,sK4),X0)
      | r2_hidden(sK5,X0) ) ),
    inference(resolution,[],[f86,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4,X0)
      | r2_hidden(sK5,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK5,X0)
      | ~ r1_tarski(sK4,X0) ) ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    r1_tarski(sK4,k1_tops_1(sK1,sK4)) ),
    inference(subsumption_resolution,[],[f85,f55])).

fof(f85,plain,
    ( ~ r1_tarski(sK4,sK4)
    | r1_tarski(sK4,k1_tops_1(sK1,sK4)) ),
    inference(subsumption_resolution,[],[f84,f28])).

fof(f84,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK4,sK4)
    | r1_tarski(sK4,k1_tops_1(sK1,sK4)) ),
    inference(resolution,[],[f83,f23])).

fof(f23,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X0,sK4)
      | r1_tarski(X0,k1_tops_1(sK1,sK4)) ) ),
    inference(subsumption_resolution,[],[f82,f36])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v3_pre_topc(X0,sK1)
      | ~ r1_tarski(X0,sK4)
      | r1_tarski(X0,k1_tops_1(sK1,sK4)) ) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f101,plain,
    ( ~ r2_hidden(sK5,k1_tops_1(sK1,sK4))
    | m1_connsp_2(sK4,sK1,sK5) ),
    inference(resolution,[],[f100,f27])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k1_tops_1(sK1,sK4))
      | m1_connsp_2(sK4,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f99,f34])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ r2_hidden(X0,k1_tops_1(sK1,sK4))
      | m1_connsp_2(sK4,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ r2_hidden(X0,k1_tops_1(sK1,sK4))
      | m1_connsp_2(sK4,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ r2_hidden(X0,k1_tops_1(sK1,sK4))
      | m1_connsp_2(sK4,sK1,X0) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK1,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(subsumption_resolution,[],[f122,f57])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(subsumption_resolution,[],[f121,f27])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(resolution,[],[f119,f59])).

fof(f59,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f20,f26])).

fof(f20,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f118,f29])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(resolution,[],[f117,f30])).

fof(f117,plain,(
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
    inference(subsumption_resolution,[],[f116,f33])).

fof(f116,plain,(
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
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,(
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
    inference(subsumption_resolution,[],[f114,f37])).

fof(f114,plain,(
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
    inference(subsumption_resolution,[],[f113,f36])).

fof(f113,plain,(
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
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,(
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
    inference(subsumption_resolution,[],[f111,f34])).

fof(f111,plain,(
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
    inference(subsumption_resolution,[],[f110,f39])).

fof(f110,plain,(
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
    inference(resolution,[],[f109,f32])).

fof(f109,plain,(
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
    inference(resolution,[],[f54,f31])).

fof(f54,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f58,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f21,f26])).

fof(f21,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13930)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (13930)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (13939)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(global_subsumption,[],[f58,f126,f139])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.51    inference(forward_demodulation,[],[f22,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    sK5 = sK6),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f7])).
% 0.22/0.51  fof(f7,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.22/0.51  % (13947)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.22/0.51    inference(resolution,[],[f136,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f135,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f131,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f130,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    v2_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f128,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f127,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) )),
% 0.22/0.51    inference(resolution,[],[f126,f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r1_tmap_1(X1,X0,sK2,X3) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~v2_pre_topc(X0) | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X3)) )),
% 0.22/0.51    inference(resolution,[],[f52,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.22/0.51    inference(equality_resolution,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f125,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ~r1_tarski(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.22/0.51    inference(resolution,[],[f123,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    m1_connsp_2(sK4,sK1,sK5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f101,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    r2_hidden(sK5,k1_tops_1(sK1,sK4))),
% 0.22/0.51    inference(resolution,[],[f87,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k1_tops_1(sK1,sK4),X0) | r2_hidden(sK5,X0)) )),
% 0.22/0.51    inference(resolution,[],[f86,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(sK4,X0) | r2_hidden(sK5,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f64,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK5,X0) | ~r1_tarski(sK4,X0)) )),
% 0.22/0.51    inference(resolution,[],[f49,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    r2_hidden(sK5,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    r1_tarski(sK4,k1_tops_1(sK1,sK4))),
% 0.22/0.51    inference(subsumption_resolution,[],[f85,f55])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~r1_tarski(sK4,sK4) | r1_tarski(sK4,k1_tops_1(sK1,sK4))),
% 0.22/0.51    inference(subsumption_resolution,[],[f84,f28])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK4,sK4) | r1_tarski(sK4,k1_tops_1(sK1,sK4))),
% 0.22/0.51    inference(resolution,[],[f83,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    v3_pre_topc(sK4,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,sK4) | r1_tarski(X0,k1_tops_1(sK1,sK4))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f82,f36])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v3_pre_topc(X0,sK1) | ~r1_tarski(X0,sK4) | r1_tarski(X0,k1_tops_1(sK1,sK4))) )),
% 0.22/0.51    inference(resolution,[],[f40,f28])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~r2_hidden(sK5,k1_tops_1(sK1,sK4)) | m1_connsp_2(sK4,sK1,sK5)),
% 0.22/0.51    inference(resolution,[],[f100,f27])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,k1_tops_1(sK1,sK4)) | m1_connsp_2(sK4,sK1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f99,f34])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~r2_hidden(X0,k1_tops_1(sK1,sK4)) | m1_connsp_2(sK4,sK1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f98,f36])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~r2_hidden(X0,k1_tops_1(sK1,sK4)) | m1_connsp_2(sK4,sK1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f35])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~r2_hidden(X0,k1_tops_1(sK1,sK4)) | m1_connsp_2(sK4,sK1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f41,f28])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK1,sK5) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f57])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f121,f27])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.22/0.51    inference(resolution,[],[f119,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.22/0.51    inference(forward_demodulation,[],[f20,f26])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f118,f29])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,X1) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.22/0.51    inference(resolution,[],[f117,f30])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f116,f33])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f115,f38])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f114,f37])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f36])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f35])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f111,f34])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f39])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.22/0.51    inference(resolution,[],[f109,f32])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) )),
% 0.22/0.51    inference(resolution,[],[f54,f31])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.22/0.51    inference(equality_resolution,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.22/0.51    inference(forward_demodulation,[],[f21,f26])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (13930)------------------------------
% 0.22/0.51  % (13930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13930)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (13930)Memory used [KB]: 6396
% 0.22/0.51  % (13930)Time elapsed: 0.101 s
% 0.22/0.51  % (13930)------------------------------
% 0.22/0.51  % (13930)------------------------------
% 0.22/0.52  % (13923)Success in time 0.149 s
%------------------------------------------------------------------------------
