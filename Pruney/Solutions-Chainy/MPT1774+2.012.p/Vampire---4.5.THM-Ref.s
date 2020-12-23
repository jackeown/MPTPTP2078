%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (3738 expanded)
%              Number of leaves         :   20 (1938 expanded)
%              Depth                    :   30
%              Number of atoms          : 1109 (89159 expanded)
%              Number of equality atoms :   34 (4741 expanded)
%              Maximal formula depth    :   31 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (11652)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (11651)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f1766,plain,(
    $false ),
    inference(global_subsumption,[],[f98,f1757,f1764])).

fof(f1764,plain,(
    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f52,f53,f54,f58,f60,f59,f61,f62,f65,f99,f266,f246,f245,f67,f63,f64,f1757,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK0,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK1)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                  & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X1)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK0,X4,X6) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,sK0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,sK1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK0,X4,X6) )
                            & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | r1_tmap_1(X3,sK0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(X2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,sK1)
                            & m1_subset_1(X7,u1_struct_0(X2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK0,X4,X6) )
                          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | r1_tmap_1(X3,sK0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(sK2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,sK1)
                          & m1_subset_1(X7,u1_struct_0(sK2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK0,X4,X6) )
                        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | r1_tmap_1(X3,sK0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(sK2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK1)
                        & m1_subset_1(X7,u1_struct_0(sK2)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | r1_tmap_1(sK3,sK0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(sK2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,sK1)
                      & m1_subset_1(X7,u1_struct_0(sK2)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | r1_tmap_1(sK3,sK0,X4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,sK1)
                    & m1_subset_1(X7,u1_struct_0(sK2)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                  & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | r1_tmap_1(sK3,sK0,sK4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(sK2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,sK1)
                  & m1_subset_1(X7,u1_struct_0(sK2)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | r1_tmap_1(sK3,sK0,sK4,X6) )
                & X6 = X7
                & r1_tarski(X5,u1_struct_0(sK2))
                & r2_hidden(X6,X5)
                & v3_pre_topc(X5,sK1)
                & m1_subset_1(X7,u1_struct_0(sK2)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
              & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | r1_tmap_1(sK3,sK0,sK4,X6) )
              & X6 = X7
              & r1_tarski(sK5,u1_struct_0(sK2))
              & r2_hidden(X6,sK5)
              & v3_pre_topc(sK5,sK1)
              & m1_subset_1(X7,u1_struct_0(sK2)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
            & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | r1_tmap_1(sK3,sK0,sK4,X6) )
            & X6 = X7
            & r1_tarski(sK5,u1_struct_0(sK2))
            & r2_hidden(X6,sK5)
            & v3_pre_topc(sK5,sK1)
            & m1_subset_1(X7,u1_struct_0(sK2)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | r1_tmap_1(sK3,sK0,sK4,sK6) )
          & sK6 = X7
          & r1_tarski(sK5,u1_struct_0(sK2))
          & r2_hidden(sK6,sK5)
          & v3_pre_topc(sK5,sK1)
          & m1_subset_1(X7,u1_struct_0(sK2)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | r1_tmap_1(sK3,sK0,sK4,sK6) )
        & sK6 = X7
        & r1_tarski(sK5,u1_struct_0(sK2))
        & r2_hidden(sK6,sK5)
        & v3_pre_topc(sK5,sK1)
        & m1_subset_1(X7,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
      & sK6 = sK7
      & r1_tarski(sK5,u1_struct_0(sK2))
      & r2_hidden(sK6,sK5)
      & v3_pre_topc(sK5,sK1)
      & m1_subset_1(sK7,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f245,plain,(
    m1_subset_1(sK9(sK3,sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f60,f152,f151,f70,f67,f223,f240,f78])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK8(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK8(X0,X1),X1)
                & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK9(X0,X1,X4),X1)
                    & m1_connsp_2(sK9(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f46,f48,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK8(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK9(X0,X1,X4),X1)
        & m1_connsp_2(sK9(X0,X1,X4),X0,X4)
        & m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f240,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(unit_resulting_resolution,[],[f57,f61,f69,f66,f223,f93])).

fof(f93,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f223,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f151,f65,f200,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f200,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f71,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f71,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f151,plain,(
    l1_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f57,f61,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f152,plain,(
    v2_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f56,f57,f61,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
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
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f246,plain,(
    m1_connsp_2(sK9(sK3,sK5,sK6),sK3,sK6) ),
    inference(unit_resulting_resolution,[],[f60,f152,f151,f70,f67,f223,f240,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_connsp_2(sK9(X0,X1,X4),X0,X4)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f266,plain,(
    r1_tarski(sK9(sK3,sK5,sK6),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f71,f247,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f247,plain,(
    r1_tarski(sK9(sK3,sK5,sK6),sK5) ),
    inference(unit_resulting_resolution,[],[f60,f152,f151,f70,f67,f223,f240,f80])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK9(X0,X1,X4),X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f68,f72])).

fof(f72,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f1757,plain,(
    r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(unit_resulting_resolution,[],[f246,f266,f1756])).

fof(f1756,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(subsumption_resolution,[],[f1755,f55])).

fof(f1755,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f1754,f56])).

fof(f1754,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f1753,f57])).

fof(f1753,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f1752,f61])).

fof(f1752,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(duplicate_literal_removal,[],[f1751])).

fof(f1751,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | r1_tmap_1(sK3,sK0,sK4,sK6) ) ),
    inference(resolution,[],[f1628,f97])).

fof(f97,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(backward_demodulation,[],[f73,f72])).

fof(f73,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f1628,plain,(
    ! [X2,X3] :
      ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6)
      | ~ m1_connsp_2(X2,sK3,sK6)
      | ~ r1_tarski(X2,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f1627,f581])).

fof(f581,plain,(
    ! [X0] :
      ( r1_tarski(X0,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f575,f90])).

fof(f575,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X3,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f567,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f567,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f178,f65])).

fof(f178,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X2,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f151,f76])).

fof(f1627,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,u1_struct_0(sK2))
      | ~ m1_connsp_2(X2,sK3,sK6)
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r1_tarski(X2,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f1626,f58])).

fof(f1626,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,u1_struct_0(sK2))
      | ~ m1_connsp_2(X2,sK3,sK6)
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r1_tarski(X2,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f1618,f65])).

fof(f1618,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,u1_struct_0(sK2))
      | ~ m1_connsp_2(X2,sK3,sK6)
      | ~ m1_pre_topc(sK2,sK3)
      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r1_tarski(X2,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f1195,f99])).

fof(f1195,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK6,u1_struct_0(X4))
      | ~ r1_tarski(X5,u1_struct_0(X4))
      | ~ m1_connsp_2(X5,sK3,sK6)
      | ~ m1_pre_topc(X4,sK3)
      | ~ r1_tmap_1(X4,sK0,k3_tmap_1(X6,sK0,sK3,X4,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r1_tarski(X5,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f902,f67])).

fof(f902,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ r1_tarski(X4,u1_struct_0(X5))
      | ~ m1_connsp_2(X4,sK3,X6)
      | ~ m1_pre_topc(X5,sK3)
      | ~ r1_tmap_1(X5,sK0,k3_tmap_1(X7,sK0,sK3,X5,sK4),X6)
      | r1_tmap_1(sK3,sK0,sK4,X6)
      | ~ m1_pre_topc(sK3,X7)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ r1_tarski(X4,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f443,f90])).

fof(f443,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_connsp_2(X0,sK3,X1)
      | ~ m1_pre_topc(X2,sK3)
      | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f442,f52])).

fof(f442,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,sK3,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X2,sK3)
      | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(X2)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f441,f53])).

fof(f441,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,sK3,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X2,sK3)
      | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f440,f54])).

fof(f440,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,sK3,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X2,sK3)
      | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f439,f60])).

fof(f439,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,sK3,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X2,sK3)
      | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
      | r1_tmap_1(sK3,sK0,sK4,X1)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(sK3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f437,f63])).

fof(f437,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,sK3,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X2,sK3)
      | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      | r1_tmap_1(sK3,sK0,sK4,X1)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(sK3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f148,f64])).

fof(f148,plain,(
    ! [X14,X12,X15,X13,X11,X16] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12))))
      | ~ m1_connsp_2(X16,X14,X15)
      | ~ r1_tarski(X16,u1_struct_0(X11))
      | ~ m1_subset_1(X15,u1_struct_0(X11))
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_pre_topc(X11,X14)
      | ~ r1_tmap_1(X11,X12,k3_tmap_1(X13,X12,X14,X11,sK4),X15)
      | ~ v1_funct_2(sK4,u1_struct_0(X14),u1_struct_0(X12))
      | r1_tmap_1(X14,X12,sK4,X15)
      | ~ m1_pre_topc(X14,X13)
      | v2_struct_0(X14)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13) ) ),
    inference(subsumption_resolution,[],[f146,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f146,plain,(
    ! [X14,X12,X15,X13,X11,X16] :
      ( ~ r1_tmap_1(X11,X12,k3_tmap_1(X13,X12,X14,X11,sK4),X15)
      | ~ m1_connsp_2(X16,X14,X15)
      | ~ r1_tarski(X16,u1_struct_0(X11))
      | ~ m1_subset_1(X15,u1_struct_0(X11))
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_pre_topc(X11,X14)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12))))
      | ~ v1_funct_2(sK4,u1_struct_0(X14),u1_struct_0(X12))
      | r1_tmap_1(X14,X12,sK4,X15)
      | ~ m1_pre_topc(X14,X13)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X11,X13)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13) ) ),
    inference(resolution,[],[f62,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(backward_demodulation,[],[f74,f72])).

fof(f74,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (11656)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (11649)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (11641)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (11650)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (11644)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (11655)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (11646)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (11653)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (11645)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (11643)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (11647)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (11648)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (11661)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (11659)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (11642)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (11660)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (11654)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (11657)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (11656)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (11652)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (11651)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f1766,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(global_subsumption,[],[f98,f1757,f1764])).
% 0.20/0.51  fof(f1764,plain,(
% 0.20/0.51    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f55,f56,f57,f52,f53,f54,f58,f60,f59,f61,f62,f65,f99,f266,f246,f245,f67,f63,f64,f1757,f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    m1_subset_1(sK9(sK3,sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f60,f152,f151,f70,f67,f223,f240,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X4,X0,X1] : (m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK8(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK9(X0,X1,X4),X1) & m1_connsp_2(sK9(X0,X1,X4),X0,X4) & m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f46,f48,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK8(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK9(X0,X1,X4),X1) & m1_connsp_2(sK9(X0,X1,X4),X0,X4) & m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    v3_pre_topc(sK5,sK3)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f57,f61,f69,f66,f223,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X3,X2)) )),
% 0.20/0.51    inference(equality_resolution,[],[f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    v3_pre_topc(sK5,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f151,f65,f200,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f71,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    r2_hidden(sK6,sK5)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    l1_pre_topc(sK3)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f57,f61,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    v2_pre_topc(sK3)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f56,f57,f61,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.52  fof(f246,plain,(
% 0.20/0.52    m1_connsp_2(sK9(sK3,sK5,sK6),sK3,sK6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f60,f152,f151,f70,f67,f223,f240,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_connsp_2(sK9(X0,X1,X4),X0,X4) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f49])).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    r1_tarski(sK9(sK3,sK5,sK6),u1_struct_0(sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f71,f247,f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.52  fof(f247,plain,(
% 0.20/0.52    r1_tarski(sK9(sK3,sK5,sK6),sK5)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f60,f152,f151,f70,f67,f223,f240,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK9(X0,X1,X4),X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f49])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f68,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    sK6 = sK7),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~v2_struct_0(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ~v2_struct_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    l1_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    v2_pre_topc(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ~v2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f1757,plain,(
% 0.20/0.52    r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f246,f266,f1756])).
% 0.20/0.52  fof(f1756,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f1755,f55])).
% 0.20/0.52  fof(f1755,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK0,sK4,sK6) | v2_struct_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f1754,f56])).
% 0.20/0.52  fof(f1754,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f1753,f57])).
% 0.20/0.52  fof(f1753,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f1752,f61])).
% 0.20/0.52  fof(f1752,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f1751])).
% 0.20/0.52  fof(f1751,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK6)) )),
% 0.20/0.52    inference(resolution,[],[f1628,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.20/0.52    inference(backward_demodulation,[],[f73,f72])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f1628,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6) | ~m1_connsp_2(X2,sK3,sK6) | ~r1_tarski(X2,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f1627,f581])).
% 0.20/0.52  fof(f581,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.20/0.52    inference(resolution,[],[f575,f90])).
% 0.20/0.52  fof(f575,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X3,u1_struct_0(sK3))) )),
% 0.20/0.52    inference(resolution,[],[f567,f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f51])).
% 0.20/0.52  fof(f567,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.52    inference(resolution,[],[f178,f65])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_pre_topc(X2,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.20/0.52    inference(resolution,[],[f151,f76])).
% 0.20/0.52  fof(f1627,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(X2,u1_struct_0(sK2)) | ~m1_connsp_2(X2,sK3,sK6) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r1_tarski(X2,u1_struct_0(sK3))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f1626,f58])).
% 0.20/0.52  fof(f1626,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(X2,u1_struct_0(sK2)) | ~m1_connsp_2(X2,sK3,sK6) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r1_tarski(X2,u1_struct_0(sK3))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f1618,f65])).
% 0.20/0.52  fof(f1618,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(X2,u1_struct_0(sK2)) | ~m1_connsp_2(X2,sK3,sK6) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X3,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r1_tarski(X2,u1_struct_0(sK3))) )),
% 0.20/0.52    inference(resolution,[],[f1195,f99])).
% 0.20/0.52  fof(f1195,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (~m1_subset_1(sK6,u1_struct_0(X4)) | ~r1_tarski(X5,u1_struct_0(X4)) | ~m1_connsp_2(X5,sK3,sK6) | ~m1_pre_topc(X4,sK3) | ~r1_tmap_1(X4,sK0,k3_tmap_1(X6,sK0,sK3,X4,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X4) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~r1_tarski(X5,u1_struct_0(sK3))) )),
% 0.20/0.52    inference(resolution,[],[f902,f67])).
% 0.20/0.52  fof(f902,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~r1_tarski(X4,u1_struct_0(X5)) | ~m1_connsp_2(X4,sK3,X6) | ~m1_pre_topc(X5,sK3) | ~r1_tmap_1(X5,sK0,k3_tmap_1(X7,sK0,sK3,X5,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,X6) | ~m1_pre_topc(sK3,X7) | v2_struct_0(X5) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~r1_tarski(X4,u1_struct_0(sK3))) )),
% 0.20/0.52    inference(resolution,[],[f443,f90])).
% 0.20/0.52  fof(f443,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK3,X1) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f442,f52])).
% 0.20/0.52  fof(f442,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X2) | v2_struct_0(sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f441,f53])).
% 0.20/0.52  fof(f441,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f440,f54])).
% 0.20/0.52  fof(f440,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f439,f60])).
% 0.20/0.52  fof(f439,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f437,f63])).
% 0.20/0.52  fof(f437,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | r1_tmap_1(sK3,sK0,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.20/0.52    inference(resolution,[],[f148,f64])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ( ! [X14,X12,X15,X13,X11,X16] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) | ~m1_connsp_2(X16,X14,X15) | ~r1_tarski(X16,u1_struct_0(X11)) | ~m1_subset_1(X15,u1_struct_0(X11)) | ~m1_subset_1(X15,u1_struct_0(X14)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14))) | ~m1_pre_topc(X11,X14) | ~r1_tmap_1(X11,X12,k3_tmap_1(X13,X12,X14,X11,sK4),X15) | ~v1_funct_2(sK4,u1_struct_0(X14),u1_struct_0(X12)) | r1_tmap_1(X14,X12,sK4,X15) | ~m1_pre_topc(X14,X13) | v2_struct_0(X14) | v2_struct_0(X11) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f146,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    ( ! [X14,X12,X15,X13,X11,X16] : (~r1_tmap_1(X11,X12,k3_tmap_1(X13,X12,X14,X11,sK4),X15) | ~m1_connsp_2(X16,X14,X15) | ~r1_tarski(X16,u1_struct_0(X11)) | ~m1_subset_1(X15,u1_struct_0(X11)) | ~m1_subset_1(X15,u1_struct_0(X14)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14))) | ~m1_pre_topc(X11,X14) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) | ~v1_funct_2(sK4,u1_struct_0(X14),u1_struct_0(X12)) | r1_tmap_1(X14,X12,sK4,X15) | ~m1_pre_topc(X14,X13) | v2_struct_0(X14) | ~m1_pre_topc(X11,X13) | v2_struct_0(X11) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13)) )),
% 0.20/0.52    inference(resolution,[],[f62,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.20/0.52    inference(backward_demodulation,[],[f74,f72])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (11656)------------------------------
% 0.20/0.52  % (11656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11656)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (11656)Memory used [KB]: 8443
% 0.20/0.52  % (11656)Time elapsed: 0.096 s
% 0.20/0.52  % (11656)------------------------------
% 0.20/0.52  % (11656)------------------------------
% 0.20/0.52  % (11640)Success in time 0.162 s
%------------------------------------------------------------------------------
