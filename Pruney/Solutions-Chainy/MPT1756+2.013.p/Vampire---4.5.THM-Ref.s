%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 403 expanded)
%              Number of leaves         :   11 (  76 expanded)
%              Depth                    :   39
%              Number of atoms          :  935 (5305 expanded)
%              Number of equality atoms :   13 ( 228 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f72,f146,f177,f192,f223])).

fof(f223,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f221,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
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

% (6920)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
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

fof(f221,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f220,f64])).

fof(f64,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_1
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f220,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f219,f60])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f24,f28])).

fof(f28,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f219,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f218,f29])).

fof(f29,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f218,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f217,f32])).

fof(f32,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f217,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f216,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f216,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f215,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f215,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f214,f34])).

fof(f34,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f214,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f213,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f213,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f212,f38])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f212,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f211,f37])).

fof(f37,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f211,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f210,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f210,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f209,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f194,f40])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f194,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
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
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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

fof(f69,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl9_2
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f192,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f190,f36])).

fof(f190,plain,
    ( v2_struct_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f189,f137])).

fof(f137,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_5
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f189,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f188,f38])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f187,f37])).

fof(f187,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f186,f155])).

fof(f155,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl9_7
  <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f186,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f185,f29])).

fof(f185,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | v2_struct_0(sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f183,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK8(X0,X1,X2),X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
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
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
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
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f183,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f182,f36])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f181,f38])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f180,f37])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f179,f137])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f106,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK8(X0,X1,X2),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f106,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X4,sK1,X3) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f105,f36])).

fof(f105,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X4,sK1,X3)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f104,f38])).

fof(f104,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X4,sK1,X3)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f98,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X4,sK1,X3)
        | v2_struct_0(sK1) )
    | spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f94,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f93,f65])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f92,f39])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f91,f60])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f90,f29])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f88,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f86,f34])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f83,f37])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f82,f36])).

fof(f82,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f19])).

% (6917)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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

fof(f68,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f177,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl9_7 ),
    inference(subsumption_resolution,[],[f175,f32])).

fof(f175,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | spl9_7 ),
    inference(subsumption_resolution,[],[f174,f27])).

fof(f27,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f174,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK1)
    | spl9_7 ),
    inference(subsumption_resolution,[],[f173,f26])).

fof(f26,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f173,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK1)
    | spl9_7 ),
    inference(resolution,[],[f156,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(u1_struct_0(X1),sK1,X0)
      | ~ r2_hidden(X0,sK4)
      | ~ r1_tarski(sK4,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f111,f74])).

fof(f74,plain,(
    ! [X2] :
      ( m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_hidden(X2,sK4) ) ),
    inference(resolution,[],[f30,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_tarski(sK4,u1_struct_0(X1))
      | ~ r2_hidden(X0,sK4)
      | m1_connsp_2(u1_struct_0(X1),sK1,X0)
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f107,f38])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_tarski(sK4,u1_struct_0(X1))
      | ~ r2_hidden(X0,sK4)
      | m1_connsp_2(u1_struct_0(X1),sK1,X0)
      | ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f78,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_tarski(sK4,X1)
      | ~ r2_hidden(X0,sK4)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f77,f25])).

fof(f25,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(sK4,sK1)
      | ~ r1_tarski(sK4,X1)
      | ~ r2_hidden(X0,sK4)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ v3_pre_topc(sK4,sK1)
      | ~ r1_tarski(sK4,X1)
      | ~ r2_hidden(X0,sK4)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ v3_pre_topc(sK4,sK1)
      | ~ r1_tarski(sK4,X1)
      | ~ r2_hidden(X0,sK4)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ v3_pre_topc(sK4,sK1)
      | ~ r1_tarski(sK4,X1)
      | ~ r2_hidden(X0,sK4)
      | m1_connsp_2(X1,sK1,X0) ) ),
    inference(resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f156,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f146,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl9_5 ),
    inference(subsumption_resolution,[],[f144,f38])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK1)
    | spl9_5 ),
    inference(subsumption_resolution,[],[f143,f32])).

fof(f143,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | spl9_5 ),
    inference(resolution,[],[f138,f42])).

fof(f138,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f72,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f71,f67,f63])).

fof(f71,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f22,f28])).

fof(f22,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f61,f67,f63])).

fof(f61,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f23,f28])).

fof(f23,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (6907)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (6913)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (6915)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (6919)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (6904)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (6916)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (6901)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6902)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (6901)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f70,f72,f146,f177,f192,f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~spl9_1 | spl9_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    $false | (~spl9_1 | spl9_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f221,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  % (6920)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    v2_struct_0(sK0) | (~spl9_1 | spl9_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f220,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    r1_tmap_1(sK1,sK0,sK2,sK5) | ~spl9_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl9_1 <=> r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f219,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f24,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    sK5 = sK6),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f218,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f217,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f216,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f215,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f214,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f213,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f212,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f211,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f210,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f209,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f194,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | v2_struct_0(sK0) | spl9_2),
% 0.21/0.50    inference(resolution,[],[f69,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | spl9_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl9_2 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    spl9_1 | ~spl9_2 | ~spl9_5 | ~spl9_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    $false | (spl9_1 | ~spl9_2 | ~spl9_5 | ~spl9_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f190,f36])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    v2_struct_0(sK1) | (spl9_1 | ~spl9_2 | ~spl9_5 | ~spl9_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl9_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl9_5 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | (spl9_1 | ~spl9_2 | ~spl9_5 | ~spl9_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f38])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | (spl9_1 | ~spl9_2 | ~spl9_5 | ~spl9_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f37])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | (spl9_1 | ~spl9_2 | ~spl9_5 | ~spl9_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~spl9_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl9_7 <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f29])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f184])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | v2_struct_0(sK1) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.50    inference(resolution,[],[f183,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_connsp_2(sK8(X0,X1,X2),X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f182,f36])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f181,f38])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f180,f37])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f179,f137])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(sK8(sK1,X0,u1_struct_0(sK3)),sK1,sK5) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.50    inference(resolution,[],[f106,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(sK8(X0,X1,X2),X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3)) | ~m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X4,sK1,X3)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f105,f36])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3)) | ~m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X4,sK1,X3) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f104,f38])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3)) | ~m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5) | ~l1_pre_topc(sK1) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X4,sK1,X3) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f98,f37])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~r1_tarski(sK8(sK1,X3,X4),u1_struct_0(sK3)) | ~m1_connsp_2(sK8(sK1,X3,X4),sK1,sK5) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X4,sK1,X3) | v2_struct_0(sK1)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.50    inference(resolution,[],[f94,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK5) | spl9_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f92,f39])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f60])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f29])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f89,f32])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f88,f31])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f87,f35])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f34])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f33])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f38])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f83,f37])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f82,f36])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f41])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f40])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | ~spl9_2),
% 0.21/0.51    inference(resolution,[],[f68,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.51    inference(equality_resolution,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  % (6917)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl9_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    $false | spl9_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f175,f32])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK1) | spl9_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f174,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r1_tarski(sK4,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1) | spl9_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f173,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    r2_hidden(sK5,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~r2_hidden(sK5,sK4) | ~r1_tarski(sK4,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1) | spl9_7),
% 0.21/0.51    inference(resolution,[],[f156,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_connsp_2(u1_struct_0(X1),sK1,X0) | ~r2_hidden(X0,sK4) | ~r1_tarski(sK4,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2] : (m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_hidden(X2,sK4)) )),
% 0.21/0.51    inference(resolution,[],[f30,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tarski(sK4,u1_struct_0(X1)) | ~r2_hidden(X0,sK4) | m1_connsp_2(u1_struct_0(X1),sK1,X0) | ~m1_pre_topc(X1,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f38])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tarski(sK4,u1_struct_0(X1)) | ~r2_hidden(X0,sK4) | m1_connsp_2(u1_struct_0(X1),sK1,X0) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f78,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tarski(sK4,X1) | ~r2_hidden(X0,sK4) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f77,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v3_pre_topc(sK4,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(sK4,sK1) | ~r1_tarski(sK4,X1) | ~r2_hidden(X0,sK4) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f76,f36])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(sK4,sK1) | ~r1_tarski(sK4,X1) | ~r2_hidden(X0,sK4) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f38])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(sK4,sK1) | ~r1_tarski(sK4,X1) | ~r2_hidden(X0,sK4) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f37])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(sK4,sK1) | ~r1_tarski(sK4,X1) | ~r2_hidden(X0,sK4) | m1_connsp_2(X1,sK1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f30,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | spl9_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    spl9_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    $false | spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f38])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f32])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | spl9_5),
% 0.21/0.51    inference(resolution,[],[f138,f42])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl9_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl9_1 | spl9_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f71,f67,f63])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f22,f28])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~spl9_1 | ~spl9_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f61,f67,f63])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f23,f28])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (6901)------------------------------
% 0.21/0.51  % (6901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6901)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (6901)Memory used [KB]: 10746
% 0.21/0.51  % (6901)Time elapsed: 0.078 s
% 0.21/0.51  % (6901)------------------------------
% 0.21/0.51  % (6901)------------------------------
% 0.21/0.51  % (6906)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (6918)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (6905)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (6899)Success in time 0.151 s
%------------------------------------------------------------------------------
