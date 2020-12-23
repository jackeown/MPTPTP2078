%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 956 expanded)
%              Number of leaves         :   14 ( 452 expanded)
%              Depth                    :   12
%              Number of atoms          :  253 (4841 expanded)
%              Number of equality atoms :   30 (  70 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8383)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% (8382)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (8387)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (8384)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (8387)Refutation not found, incomplete strategy% (8387)------------------------------
% (8387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8387)Termination reason: Refutation not found, incomplete strategy

% (8387)Memory used [KB]: 6140
% (8387)Time elapsed: 0.107 s
% (8387)------------------------------
% (8387)------------------------------
% (8388)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (8388)Refutation not found, incomplete strategy% (8388)------------------------------
% (8388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8388)Termination reason: Refutation not found, incomplete strategy

% (8388)Memory used [KB]: 10490
% (8388)Time elapsed: 0.108 s
% (8388)------------------------------
% (8388)------------------------------
fof(f265,plain,(
    $false ),
    inference(global_subsumption,[],[f250,f264])).

fof(f264,plain,(
    u1_waybel_0(sK0,sK3) != k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) ),
    inference(superposition,[],[f244,f196])).

fof(f196,plain,(
    ! [X0] : k7_relat_1(u1_waybel_0(sK0,sK1),X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f60,f91,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f91,plain,(
    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f35,f36,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f36,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ m1_yellow_6(sK3,sK0,sK1)
    & m1_yellow_6(sK3,sK0,sK2)
    & m1_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_yellow_6(X3,X0,X1)
                    & m1_yellow_6(X3,X0,X2) )
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_yellow_6(X3,sK0,X1)
                  & m1_yellow_6(X3,sK0,X2) )
              & m1_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_yellow_6(X3,sK0,X1)
                & m1_yellow_6(X3,sK0,X2) )
            & m1_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_yellow_6(X3,sK0,sK1)
              & m1_yellow_6(X3,sK0,X2) )
          & m1_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_yellow_6(X3,sK0,sK1)
            & m1_yellow_6(X3,sK0,X2) )
        & m1_yellow_6(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ~ m1_yellow_6(X3,sK0,sK1)
          & m1_yellow_6(X3,sK0,sK2) )
      & m1_yellow_6(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ m1_yellow_6(X3,sK0,sK1)
        & m1_yellow_6(X3,sK0,sK2) )
   => ( ~ m1_yellow_6(sK3,sK0,sK1)
      & m1_yellow_6(sK3,sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_yellow_6(X3,X0,X1)
                  & m1_yellow_6(X3,X0,X2) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_yellow_6(X3,X0,X2)
                   => m1_yellow_6(X3,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_yellow_6(X3,X0,X2)
                 => m1_yellow_6(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_6)).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f244,plain,(
    u1_waybel_0(sK0,sK3) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f84,f36,f39,f64,f35,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
      | ~ m1_yellow_0(X2,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f64,plain,(
    l1_waybel_0(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f35,f38,f61,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f61,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f36,f37,f35,f51])).

fof(f37,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    m1_yellow_6(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ~ m1_yellow_6(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    m1_yellow_0(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f56,f75,f76,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ m1_yellow_0(X2,X1)
      | m1_yellow_0(X2,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_yellow_0(X2,X0)
              | ~ m1_yellow_0(X2,X1) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_6)).

fof(f76,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f61,f64,f38,f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_yellow_0(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f36,f61,f37,f35,f45])).

fof(f56,plain,(
    l1_orders_2(sK1) ),
    inference(unit_resulting_resolution,[],[f36,f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f250,plain,(
    u1_waybel_0(sK0,sK3) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f237,f248])).

fof(f248,plain,(
    u1_waybel_0(sK0,sK3) = k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) ),
    inference(superposition,[],[f232,f197])).

fof(f197,plain,(
    ! [X0] : k7_relat_1(u1_waybel_0(sK0,sK2),X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),X0) ),
    inference(unit_resulting_resolution,[],[f65,f92,f55])).

fof(f92,plain,(
    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f35,f61,f50])).

fof(f65,plain,(
    v1_funct_1(u1_waybel_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f35,f61,f48])).

fof(f232,plain,(
    u1_waybel_0(sK0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f35,f61,f64,f38,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f237,plain,(
    k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f125,f234])).

fof(f234,plain,(
    u1_waybel_0(sK0,sK2) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) ),
    inference(superposition,[],[f231,f196])).

fof(f231,plain,(
    u1_waybel_0(sK0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f61,f37,f46])).

fof(f125,plain,(
    k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) = k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2)),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f97,f60,f83,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

% (8402)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

fof(f83,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f66,f70,f76,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f70,plain,(
    l1_orders_2(sK3) ),
    inference(unit_resulting_resolution,[],[f35,f64,f44])).

fof(f66,plain,(
    l1_orders_2(sK2) ),
    inference(unit_resulting_resolution,[],[f35,f61,f44])).

fof(f97,plain,(
    v1_relat_1(u1_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f35,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_relat_1(u1_waybel_0(X1,X0))
      | ~ l1_struct_0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f50,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:35:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (8392)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (8396)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.49  % (8396)Refutation not found, incomplete strategy% (8396)------------------------------
% 0.20/0.49  % (8396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8396)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8396)Memory used [KB]: 1535
% 0.20/0.49  % (8396)Time elapsed: 0.004 s
% 0.20/0.49  % (8396)------------------------------
% 0.20/0.49  % (8396)------------------------------
% 0.20/0.49  % (8401)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.49  % (8385)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (8394)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (8397)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (8398)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (8399)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (8380)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (8381)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (8394)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (8383)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.52  % (8382)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (8387)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (8384)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.52  % (8387)Refutation not found, incomplete strategy% (8387)------------------------------
% 0.20/0.52  % (8387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8387)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8387)Memory used [KB]: 6140
% 0.20/0.52  % (8387)Time elapsed: 0.107 s
% 0.20/0.52  % (8387)------------------------------
% 0.20/0.52  % (8387)------------------------------
% 0.20/0.52  % (8388)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (8388)Refutation not found, incomplete strategy% (8388)------------------------------
% 0.20/0.52  % (8388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8388)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8388)Memory used [KB]: 10490
% 0.20/0.52  % (8388)Time elapsed: 0.108 s
% 0.20/0.52  % (8388)------------------------------
% 0.20/0.52  % (8388)------------------------------
% 1.28/0.53  fof(f265,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(global_subsumption,[],[f250,f264])).
% 1.28/0.53  fof(f264,plain,(
% 1.28/0.53    u1_waybel_0(sK0,sK3) != k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3))),
% 1.28/0.53    inference(superposition,[],[f244,f196])).
% 1.28/0.53  fof(f196,plain,(
% 1.28/0.53    ( ! [X0] : (k7_relat_1(u1_waybel_0(sK0,sK1),X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)) )),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f60,f91,f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.28/0.53    inference(flattening,[],[f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.28/0.53    inference(ennf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.28/0.53  fof(f91,plain,(
% 1.28/0.53    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f36,f50])).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.28/0.53    inference(flattening,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    l1_waybel_0(sK1,sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f30])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    (((~m1_yellow_6(sK3,sK0,sK1) & m1_yellow_6(sK3,sK0,sK2)) & m1_yellow_6(sK2,sK0,sK1)) & l1_waybel_0(sK1,sK0)) & l1_struct_0(sK0)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f29,f28,f27,f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,X2)) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,sK0,X1) & m1_yellow_6(X3,sK0,X2)) & m1_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0)) & l1_struct_0(sK0))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,sK0,X1) & m1_yellow_6(X3,sK0,X2)) & m1_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0)) => (? [X2] : (? [X3] : (~m1_yellow_6(X3,sK0,sK1) & m1_yellow_6(X3,sK0,X2)) & m1_yellow_6(X2,sK0,sK1)) & l1_waybel_0(sK1,sK0))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ? [X2] : (? [X3] : (~m1_yellow_6(X3,sK0,sK1) & m1_yellow_6(X3,sK0,X2)) & m1_yellow_6(X2,sK0,sK1)) => (? [X3] : (~m1_yellow_6(X3,sK0,sK1) & m1_yellow_6(X3,sK0,sK2)) & m1_yellow_6(sK2,sK0,sK1))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ? [X3] : (~m1_yellow_6(X3,sK0,sK1) & m1_yellow_6(X3,sK0,sK2)) => (~m1_yellow_6(sK3,sK0,sK1) & m1_yellow_6(sK3,sK0,sK2))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f12,plain,(
% 1.28/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,X2)) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,negated_conjecture,(
% 1.28/0.53    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_yellow_6(X3,X0,X2) => m1_yellow_6(X3,X0,X1)))))),
% 1.28/0.53    inference(negated_conjecture,[],[f10])).
% 1.28/0.53  fof(f10,conjecture,(
% 1.28/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_yellow_6(X3,X0,X2) => m1_yellow_6(X3,X0,X1)))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_6)).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    l1_struct_0(sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f30])).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    v1_funct_1(u1_waybel_0(sK0,sK1))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f36,f48])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f244,plain,(
% 1.28/0.53    u1_waybel_0(sK0,sK3) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f84,f36,f39,f64,f35,f47])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | m1_yellow_6(X2,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1)) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.28/0.53    inference(flattening,[],[f33])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | (u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1))) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.28/0.53    inference(nnf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).
% 1.28/0.53  fof(f64,plain,(
% 1.28/0.53    l1_waybel_0(sK3,sK0)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f38,f61,f51])).
% 1.28/0.53  fof(f51,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | l1_waybel_0(X2,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.28/0.53    inference(flattening,[],[f19])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f8])).
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).
% 1.28/0.53  fof(f61,plain,(
% 1.28/0.53    l1_waybel_0(sK2,sK0)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f36,f37,f35,f51])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    m1_yellow_6(sK2,sK0,sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f30])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    m1_yellow_6(sK3,sK0,sK2)),
% 1.28/0.53    inference(cnf_transformation,[],[f30])).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ~m1_yellow_6(sK3,sK0,sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f30])).
% 1.28/0.53  fof(f84,plain,(
% 1.28/0.53    m1_yellow_0(sK3,sK1)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f56,f75,f76,f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_yellow_0(X1,X0) | ~m1_yellow_0(X2,X1) | m1_yellow_0(X2,X0) | ~l1_orders_2(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_yellow_0(X2,X0) | ~m1_yellow_0(X2,X1)) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => ! [X2] : (m1_yellow_0(X2,X1) => m1_yellow_0(X2,X0))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_6)).
% 1.28/0.53  fof(f76,plain,(
% 1.28/0.53    m1_yellow_0(sK3,sK2)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f61,f64,f38,f35,f45])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | m1_yellow_0(X2,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f75,plain,(
% 1.28/0.53    m1_yellow_0(sK2,sK1)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f36,f61,f37,f35,f45])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    l1_orders_2(sK1)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f36,f35,f44])).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | l1_orders_2(X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 1.28/0.53  fof(f250,plain,(
% 1.28/0.53    u1_waybel_0(sK0,sK3) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3))),
% 1.28/0.53    inference(backward_demodulation,[],[f237,f248])).
% 1.28/0.53  fof(f248,plain,(
% 1.28/0.53    u1_waybel_0(sK0,sK3) = k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3))),
% 1.28/0.53    inference(superposition,[],[f232,f197])).
% 1.28/0.53  fof(f197,plain,(
% 1.28/0.53    ( ! [X0] : (k7_relat_1(u1_waybel_0(sK0,sK2),X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),X0)) )),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f65,f92,f55])).
% 1.28/0.53  fof(f92,plain,(
% 1.28/0.53    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f61,f50])).
% 1.28/0.53  fof(f65,plain,(
% 1.28/0.53    v1_funct_1(u1_waybel_0(sK0,sK2))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f61,f48])).
% 1.28/0.53  fof(f232,plain,(
% 1.28/0.53    u1_waybel_0(sK0,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f61,f64,f38,f46])).
% 1.28/0.53  fof(f46,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f237,plain,(
% 1.28/0.53    k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3))),
% 1.28/0.53    inference(backward_demodulation,[],[f125,f234])).
% 1.28/0.53  fof(f234,plain,(
% 1.28/0.53    u1_waybel_0(sK0,sK2) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2))),
% 1.28/0.53    inference(superposition,[],[f231,f196])).
% 1.28/0.53  fof(f231,plain,(
% 1.28/0.53    u1_waybel_0(sK0,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f36,f61,f37,f46])).
% 1.28/0.53  fof(f125,plain,(
% 1.28/0.53    k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) = k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2)),u1_struct_0(sK3))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f97,f60,f83,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~v1_funct_1(X2) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  % (8402)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.28/0.53    inference(flattening,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) | ~r1_tarski(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.28/0.53    inference(ennf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).
% 1.28/0.53  fof(f83,plain,(
% 1.28/0.53    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f66,f70,f76,f40])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.28/0.53    inference(flattening,[],[f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.28/0.53    inference(nnf_transformation,[],[f13])).
% 1.28/0.53  fof(f13,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).
% 1.28/0.53  fof(f70,plain,(
% 1.28/0.53    l1_orders_2(sK3)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f64,f44])).
% 1.28/0.53  fof(f66,plain,(
% 1.28/0.53    l1_orders_2(sK2)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f35,f61,f44])).
% 1.28/0.53  fof(f97,plain,(
% 1.28/0.53    v1_relat_1(u1_waybel_0(sK0,sK1))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f36,f35,f94])).
% 1.28/0.53  fof(f94,plain,(
% 1.28/0.53    ( ! [X0,X1] : (v1_relat_1(u1_waybel_0(X1,X0)) | ~l1_struct_0(X1) | ~l1_waybel_0(X0,X1)) )),
% 1.28/0.53    inference(resolution,[],[f50,f52])).
% 1.28/0.53  fof(f52,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f21])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(ennf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (8394)------------------------------
% 1.28/0.53  % (8394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (8394)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (8394)Memory used [KB]: 11001
% 1.28/0.53  % (8394)Time elapsed: 0.090 s
% 1.28/0.53  % (8394)------------------------------
% 1.28/0.53  % (8394)------------------------------
% 1.28/0.53  % (8386)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.28/0.53  % (8379)Success in time 0.169 s
%------------------------------------------------------------------------------
