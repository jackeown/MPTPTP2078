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
% DateTime   : Thu Dec  3 13:14:26 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  188 (19569 expanded)
%              Number of leaves         :   19 (3830 expanded)
%              Depth                    :   39
%              Number of atoms          :  669 (93402 expanded)
%              Number of equality atoms :  207 (15441 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(subsumption_resolution,[],[f383,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f383,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f126,f378])).

fof(f378,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f377,f206])).

fof(f206,plain,(
    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(subsumption_resolution,[],[f205,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

% (1468)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (1491)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (1495)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (1487)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (1475)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (1484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (1470)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (1475)Refutation not found, incomplete strategy% (1475)------------------------------
% (1475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1475)Termination reason: Refutation not found, incomplete strategy

% (1475)Memory used [KB]: 10746
% (1475)Time elapsed: 0.136 s
% (1475)------------------------------
% (1475)------------------------------
% (1467)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (1492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (1477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (1483)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f205,plain,
    ( ~ v1_funct_1(sK2)
    | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(subsumption_resolution,[],[f204,f138])).

fof(f138,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f120,f134])).

fof(f134,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f133,f116])).

fof(f116,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f102])).

fof(f102,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f101,f74])).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f101,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f94,f92])).

fof(f92,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f64,f59])).

fof(f59,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f53,f91])).

fof(f91,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f77,f103])).

fof(f103,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f79,f99])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f133,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f132,f120])).

fof(f132,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f131,f51])).

fof(f131,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f130,f126])).

fof(f130,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f75,f121])).

fof(f121,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f99,f118])).

fof(f118,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f98,f117])).

fof(f117,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f78,f99])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f98,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f95,f92])).

fof(f95,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f54,f91])).

fof(f54,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f120,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f100,f118])).

fof(f100,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f93,f92])).

fof(f93,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f52,f91])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f204,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    inference(resolution,[],[f201,f139])).

fof(f139,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f121,f134])).

fof(f201,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),X0,X0) ) ),
    inference(subsumption_resolution,[],[f200,f138])).

fof(f200,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),X0,X0) ) ),
    inference(subsumption_resolution,[],[f198,f51])).

fof(f198,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),X0,X0) ) ),
    inference(resolution,[],[f86,f139])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f377,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f376])).

fof(f376,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f375,f310])).

fof(f310,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f309,f51])).

fof(f309,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f308,f102])).

fof(f308,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f307])).

fof(f307,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f232,f246])).

fof(f246,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f245,f55])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f245,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f244,f137])).

fof(f137,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f119,f134])).

fof(f119,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f117,f118])).

fof(f244,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f243,f51])).

fof(f243,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f241,f138])).

fof(f241,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(resolution,[],[f85,f139])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f232,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2))
      | k1_xboole_0 = k2_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(k2_funct_1(sK2)) = X0 ) ),
    inference(subsumption_resolution,[],[f227,f189])).

fof(f189,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f173,f74])).

fof(f173,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f166,f65])).

fof(f166,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f165,f137])).

fof(f165,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f164,f55])).

fof(f164,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f163,f51])).

fof(f163,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f162,f138])).

fof(f162,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(resolution,[],[f82,f139])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f227,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK2)
      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | k2_funct_1(k2_funct_1(sK2)) = X0 ) ),
    inference(resolution,[],[f224,f161])).

fof(f161,plain,(
    ! [X0] :
      ( ~ v2_funct_1(k2_funct_1(sK2))
      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | k2_funct_1(k2_funct_1(sK2)) = X0 ) ),
    inference(forward_demodulation,[],[f160,f113])).

fof(f113,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f112,f102])).

% (1478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f110,f51])).

fof(f110,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f70,f55])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f160,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k2_funct_1(sK2))
      | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | k2_funct_1(k2_funct_1(sK2)) = X0 ) ),
    inference(subsumption_resolution,[],[f159,f153])).

fof(f153,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f152,f137])).

fof(f152,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f151,f55])).

fof(f151,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f150,f51])).

fof(f150,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f149,f138])).

fof(f149,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f80,f139])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f159,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2))
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k2_funct_1(sK2))
      | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | k2_funct_1(k2_funct_1(sK2)) = X0 ) ),
    inference(superposition,[],[f89,f107])).

fof(f107,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f106,f102])).

fof(f106,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f104,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f69,f55])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f71,f61])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f224,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f223,f107])).

fof(f223,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f222,f189])).

fof(f222,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f221,f51])).

fof(f221,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f220,f102])).

fof(f220,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f219,f153])).

fof(f219,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f217,f87])).

fof(f87,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f61])).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f217,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f73,f215])).

fof(f215,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f214,f137])).

fof(f214,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f213,f138])).

fof(f213,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f212,f139])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k2_relset_1(X0,X1,sK2) != X1
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(sK2,k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f210,f51])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(sK2,k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f84,f55])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f375,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f197,f374])).

fof(f374,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f373,f182])).

fof(f182,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f171,f113])).

fof(f171,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f166,f78])).

fof(f373,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f372,f158])).

fof(f158,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f157,f137])).

fof(f157,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f156,f55])).

fof(f156,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f155,f51])).

fof(f155,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f154,f138])).

fof(f154,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f81,f139])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f372,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f234,f166])).

fof(f234,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(k2_funct_1(sK2),X3,X4)
      | k1_xboole_0 = k2_relat_1(sK2)
      | k2_relset_1(X3,X4,k2_funct_1(sK2)) != X4
      | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X3,X4,k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f229,f153])).

fof(f229,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k2_relat_1(sK2)
      | ~ v1_funct_2(k2_funct_1(sK2),X3,X4)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k2_relset_1(X3,X4,k2_funct_1(sK2)) != X4
      | ~ v1_funct_1(k2_funct_1(sK2))
      | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X3,X4,k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f224,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f197,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f140,f196])).

fof(f196,plain,(
    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f195,f137])).

fof(f195,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f194,f138])).

fof(f194,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f193,f139])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k2_relset_1(X0,X1,sK2) != X1
      | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) ) ),
    inference(subsumption_resolution,[],[f191,f51])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v1_funct_1(sK2)
      | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) ) ),
    inference(resolution,[],[f83,f55])).

fof(f140,plain,(
    ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f122,f134])).

fof(f122,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f97,f118])).

fof(f97,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f96,f92])).

fof(f96,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f56,f91])).

fof(f56,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f126,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f125,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f125,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f124,f58])).

fof(f124,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f66,f118])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (1472)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (1473)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (1471)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (1480)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.52  % (1489)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.22/0.52  % (1488)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.53  % (1465)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.53  % (1482)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.22/0.53  % (1474)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.22/0.53  % (1481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.22/0.53  % (1479)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.53  % (1476)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.22/0.53  % (1485)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.53  % (1482)Refutation not found, incomplete strategy% (1482)------------------------------
% 1.22/0.53  % (1482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (1466)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.53  % (1490)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.22/0.53  % (1482)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (1482)Memory used [KB]: 10618
% 1.22/0.53  % (1482)Time elapsed: 0.087 s
% 1.22/0.53  % (1482)------------------------------
% 1.22/0.53  % (1482)------------------------------
% 1.22/0.53  % (1469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.53  % (1471)Refutation found. Thanks to Tanya!
% 1.22/0.53  % SZS status Theorem for theBenchmark
% 1.22/0.53  % SZS output start Proof for theBenchmark
% 1.22/0.53  fof(f406,plain,(
% 1.22/0.53    $false),
% 1.22/0.53    inference(subsumption_resolution,[],[f383,f60])).
% 1.22/0.53  fof(f60,plain,(
% 1.22/0.53    v1_xboole_0(k1_xboole_0)),
% 1.22/0.53    inference(cnf_transformation,[],[f1])).
% 1.22/0.53  fof(f1,axiom,(
% 1.22/0.53    v1_xboole_0(k1_xboole_0)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.22/0.53  fof(f383,plain,(
% 1.22/0.53    ~v1_xboole_0(k1_xboole_0)),
% 1.22/0.53    inference(backward_demodulation,[],[f126,f378])).
% 1.22/0.53  fof(f378,plain,(
% 1.22/0.53    k1_xboole_0 = k2_relat_1(sK2)),
% 1.22/0.53    inference(subsumption_resolution,[],[f377,f206])).
% 1.22/0.53  fof(f206,plain,(
% 1.22/0.53    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.22/0.53    inference(subsumption_resolution,[],[f205,f51])).
% 1.22/0.53  fof(f51,plain,(
% 1.22/0.53    v1_funct_1(sK2)),
% 1.22/0.53    inference(cnf_transformation,[],[f24])).
% 1.22/0.53  fof(f24,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.22/0.53    inference(flattening,[],[f23])).
% 1.22/0.53  fof(f23,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f21])).
% 1.36/0.54  % (1468)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.54  % (1491)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (1495)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (1487)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (1475)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.55  % (1484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (1470)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.55  % (1475)Refutation not found, incomplete strategy% (1475)------------------------------
% 1.36/0.55  % (1475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (1475)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (1475)Memory used [KB]: 10746
% 1.36/0.55  % (1475)Time elapsed: 0.136 s
% 1.36/0.55  % (1475)------------------------------
% 1.36/0.55  % (1475)------------------------------
% 1.36/0.55  % (1467)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.55  % (1492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (1477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (1483)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.56  fof(f21,negated_conjecture,(
% 1.36/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.36/0.56    inference(negated_conjecture,[],[f20])).
% 1.36/0.56  fof(f20,conjecture,(
% 1.36/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 1.36/0.56  fof(f205,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f204,f138])).
% 1.36/0.56  fof(f138,plain,(
% 1.36/0.56    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.36/0.56    inference(backward_demodulation,[],[f120,f134])).
% 1.36/0.56  fof(f134,plain,(
% 1.36/0.56    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.36/0.56    inference(resolution,[],[f133,f116])).
% 1.36/0.56  fof(f116,plain,(
% 1.36/0.56    ~v1_partfun1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f115,f102])).
% 1.36/0.56  fof(f102,plain,(
% 1.36/0.56    v1_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f101,f74])).
% 1.36/0.56  fof(f74,plain,(
% 1.36/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f3])).
% 1.36/0.56  fof(f3,axiom,(
% 1.36/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.36/0.56  fof(f101,plain,(
% 1.36/0.56    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2)),
% 1.36/0.56    inference(resolution,[],[f65,f99])).
% 1.36/0.56  fof(f99,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.36/0.56    inference(backward_demodulation,[],[f94,f92])).
% 1.36/0.56  fof(f92,plain,(
% 1.36/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.36/0.56    inference(resolution,[],[f64,f59])).
% 1.36/0.56  fof(f59,plain,(
% 1.36/0.56    l1_struct_0(sK0)),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f64,plain,(
% 1.36/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f25])).
% 1.36/0.56  fof(f25,plain,(
% 1.36/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f17])).
% 1.36/0.56  fof(f17,axiom,(
% 1.36/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.36/0.56  fof(f94,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.36/0.56    inference(backward_demodulation,[],[f53,f91])).
% 1.36/0.56  fof(f91,plain,(
% 1.36/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.36/0.56    inference(resolution,[],[f64,f58])).
% 1.36/0.56  fof(f58,plain,(
% 1.36/0.56    l1_struct_0(sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f53,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f65,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f26])).
% 1.36/0.56  fof(f26,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f2])).
% 1.36/0.56  fof(f2,axiom,(
% 1.36/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.36/0.56  fof(f115,plain,(
% 1.36/0.56    ~v1_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.36/0.56    inference(resolution,[],[f77,f103])).
% 1.36/0.56  fof(f103,plain,(
% 1.36/0.56    v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.36/0.56    inference(resolution,[],[f79,f99])).
% 1.36/0.56  fof(f79,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f42])).
% 1.36/0.56  fof(f42,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.56    inference(ennf_transformation,[],[f22])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.36/0.56    inference(pure_predicate_removal,[],[f9])).
% 1.36/0.56  fof(f9,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.56  fof(f77,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f40])).
% 1.36/0.56  fof(f40,plain,(
% 1.36/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.56    inference(flattening,[],[f39])).
% 1.36/0.56  fof(f39,plain,(
% 1.36/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.36/0.56    inference(ennf_transformation,[],[f12])).
% 1.36/0.56  fof(f12,axiom,(
% 1.36/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.36/0.56  fof(f133,plain,(
% 1.36/0.56    v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.36/0.56    inference(subsumption_resolution,[],[f132,f120])).
% 1.36/0.56  fof(f132,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.36/0.56    inference(subsumption_resolution,[],[f131,f51])).
% 1.36/0.56  fof(f131,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.36/0.56    inference(subsumption_resolution,[],[f130,f126])).
% 1.36/0.56  fof(f130,plain,(
% 1.36/0.56    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.36/0.56    inference(resolution,[],[f75,f121])).
% 1.36/0.56  fof(f121,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.36/0.56    inference(backward_demodulation,[],[f99,f118])).
% 1.36/0.56  fof(f118,plain,(
% 1.36/0.56    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f98,f117])).
% 1.36/0.56  fof(f117,plain,(
% 1.36/0.56    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.36/0.56    inference(resolution,[],[f78,f99])).
% 1.36/0.56  fof(f78,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f41])).
% 1.36/0.56  fof(f41,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.56    inference(ennf_transformation,[],[f10])).
% 1.36/0.56  fof(f10,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.56  fof(f98,plain,(
% 1.36/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f95,f92])).
% 1.36/0.56  fof(f95,plain,(
% 1.36/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f54,f91])).
% 1.36/0.56  fof(f54,plain,(
% 1.36/0.56    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f75,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f38])).
% 1.36/0.56  fof(f38,plain,(
% 1.36/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.36/0.56    inference(flattening,[],[f37])).
% 1.36/0.56  fof(f37,plain,(
% 1.36/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f11])).
% 1.36/0.56  fof(f11,axiom,(
% 1.36/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.36/0.56  fof(f120,plain,(
% 1.36/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.36/0.56    inference(backward_demodulation,[],[f100,f118])).
% 1.36/0.56  fof(f100,plain,(
% 1.36/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.36/0.56    inference(backward_demodulation,[],[f93,f92])).
% 1.36/0.56  fof(f93,plain,(
% 1.36/0.56    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 1.36/0.56    inference(backward_demodulation,[],[f52,f91])).
% 1.36/0.56  fof(f52,plain,(
% 1.36/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f204,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.36/0.56    inference(resolution,[],[f201,f139])).
% 1.36/0.56  fof(f139,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.36/0.56    inference(backward_demodulation,[],[f121,f134])).
% 1.36/0.56  fof(f201,plain,(
% 1.36/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),X0,X0)) )),
% 1.36/0.56    inference(subsumption_resolution,[],[f200,f138])).
% 1.36/0.56  fof(f200,plain,(
% 1.36/0.56    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),X0,X0)) )),
% 1.36/0.56    inference(subsumption_resolution,[],[f198,f51])).
% 1.36/0.56  fof(f198,plain,(
% 1.36/0.56    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),X0,X0)) )),
% 1.36/0.56    inference(resolution,[],[f86,f139])).
% 1.36/0.56  fof(f86,plain,(
% 1.36/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2) | r2_funct_2(X0,X1,X2,X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f50])).
% 1.36/0.56  fof(f50,plain,(
% 1.36/0.56    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.56    inference(flattening,[],[f49])).
% 1.36/0.56  fof(f49,plain,(
% 1.36/0.56    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f14])).
% 1.36/0.56  fof(f14,axiom,(
% 1.36/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.36/0.56  fof(f377,plain,(
% 1.36/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(duplicate_literal_removal,[],[f376])).
% 1.36/0.56  fof(f376,plain,(
% 1.36/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(superposition,[],[f375,f310])).
% 1.36/0.56  fof(f310,plain,(
% 1.36/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f309,f51])).
% 1.36/0.56  fof(f309,plain,(
% 1.36/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f308,f102])).
% 1.36/0.56  fof(f308,plain,(
% 1.36/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(trivial_inequality_removal,[],[f307])).
% 1.36/0.56  fof(f307,plain,(
% 1.36/0.56    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) != k1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(duplicate_literal_removal,[],[f306])).
% 1.36/0.56  fof(f306,plain,(
% 1.36/0.56    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) != k1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(superposition,[],[f232,f246])).
% 1.36/0.56  fof(f246,plain,(
% 1.36/0.56    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f245,f55])).
% 1.36/0.56  fof(f55,plain,(
% 1.36/0.56    v2_funct_1(sK2)),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f245,plain,(
% 1.36/0.56    ~v2_funct_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f244,f137])).
% 1.36/0.56  fof(f137,plain,(
% 1.36/0.56    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f119,f134])).
% 1.36/0.56  fof(f119,plain,(
% 1.36/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f117,f118])).
% 1.36/0.56  fof(f244,plain,(
% 1.36/0.56    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f243,f51])).
% 1.36/0.56  fof(f243,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f241,f138])).
% 1.36/0.56  fof(f241,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.36/0.56    inference(resolution,[],[f85,f139])).
% 1.36/0.56  fof(f85,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f48])).
% 1.36/0.56  fof(f48,plain,(
% 1.36/0.56    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.56    inference(flattening,[],[f47])).
% 1.36/0.56  fof(f47,plain,(
% 1.36/0.56    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f16])).
% 1.36/0.56  fof(f16,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.36/0.56  fof(f232,plain,(
% 1.36/0.56    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(k2_funct_1(sK2)) = X0) )),
% 1.36/0.56    inference(subsumption_resolution,[],[f227,f189])).
% 1.36/0.56  fof(f189,plain,(
% 1.36/0.56    v1_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f173,f74])).
% 1.36/0.56  fof(f173,plain,(
% 1.36/0.56    ~v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) | v1_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f166,f65])).
% 1.36/0.56  fof(f166,plain,(
% 1.36/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.36/0.56    inference(subsumption_resolution,[],[f165,f137])).
% 1.36/0.56  fof(f165,plain,(
% 1.36/0.56    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.36/0.56    inference(subsumption_resolution,[],[f164,f55])).
% 1.36/0.56  fof(f164,plain,(
% 1.36/0.56    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.36/0.56    inference(subsumption_resolution,[],[f163,f51])).
% 1.36/0.56  fof(f163,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.36/0.56    inference(subsumption_resolution,[],[f162,f138])).
% 1.36/0.56  fof(f162,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.36/0.56    inference(resolution,[],[f82,f139])).
% 1.36/0.56  fof(f82,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f44])).
% 1.36/0.56  fof(f44,plain,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.56    inference(flattening,[],[f43])).
% 1.36/0.56  fof(f43,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f15])).
% 1.36/0.56  fof(f15,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.36/0.56  fof(f227,plain,(
% 1.36/0.56    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK2) | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0) )),
% 1.36/0.56    inference(resolution,[],[f224,f161])).
% 1.36/0.56  fof(f161,plain,(
% 1.36/0.56    ( ! [X0] : (~v2_funct_1(k2_funct_1(sK2)) | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0) )),
% 1.36/0.56    inference(forward_demodulation,[],[f160,f113])).
% 1.36/0.56  fof(f113,plain,(
% 1.36/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f112,f102])).
% 1.36/0.56  % (1478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.56  fof(f112,plain,(
% 1.36/0.56    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f110,f51])).
% 1.36/0.56  fof(f110,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f70,f55])).
% 1.36/0.56  fof(f70,plain,(
% 1.36/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f32])).
% 1.36/0.56  fof(f32,plain,(
% 1.36/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.56    inference(flattening,[],[f31])).
% 1.36/0.56  fof(f31,plain,(
% 1.36/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f7])).
% 1.36/0.56  fof(f7,axiom,(
% 1.36/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.36/0.56  fof(f160,plain,(
% 1.36/0.56    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k2_funct_1(sK2)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0) )),
% 1.36/0.56    inference(subsumption_resolution,[],[f159,f153])).
% 1.36/0.56  fof(f153,plain,(
% 1.36/0.56    v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f152,f137])).
% 1.36/0.56  fof(f152,plain,(
% 1.36/0.56    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f151,f55])).
% 1.36/0.56  fof(f151,plain,(
% 1.36/0.56    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f150,f51])).
% 1.36/0.56  fof(f150,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f149,f138])).
% 1.36/0.56  fof(f149,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f80,f139])).
% 1.36/0.56  fof(f80,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f44])).
% 1.36/0.56  fof(f159,plain,(
% 1.36/0.56    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k2_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k2_funct_1(sK2)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0) )),
% 1.36/0.56    inference(superposition,[],[f89,f107])).
% 1.36/0.56  fof(f107,plain,(
% 1.36/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f106,f102])).
% 1.36/0.56  fof(f106,plain,(
% 1.36/0.56    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f104,f51])).
% 1.36/0.56  fof(f104,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f69,f55])).
% 1.36/0.56  fof(f69,plain,(
% 1.36/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f32])).
% 1.36/0.56  fof(f89,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.36/0.56    inference(definition_unfolding,[],[f71,f61])).
% 1.36/0.56  fof(f61,plain,(
% 1.36/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f13])).
% 1.36/0.56  fof(f13,axiom,(
% 1.36/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.36/0.56  fof(f71,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f34])).
% 1.36/0.56  fof(f34,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.56    inference(flattening,[],[f33])).
% 1.36/0.56  fof(f33,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f8])).
% 1.36/0.56  fof(f8,axiom,(
% 1.36/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.36/0.56  fof(f224,plain,(
% 1.36/0.56    v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f223,f107])).
% 1.36/0.56  fof(f223,plain,(
% 1.36/0.56    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f222,f189])).
% 1.36/0.56  fof(f222,plain,(
% 1.36/0.56    ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f221,f51])).
% 1.36/0.56  fof(f221,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f220,f102])).
% 1.36/0.56  fof(f220,plain,(
% 1.36/0.56    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f219,f153])).
% 1.36/0.56  fof(f219,plain,(
% 1.36/0.56    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f217,f87])).
% 1.36/0.56  fof(f87,plain,(
% 1.36/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.36/0.56    inference(definition_unfolding,[],[f63,f61])).
% 1.36/0.56  fof(f63,plain,(
% 1.36/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f5])).
% 1.36/0.56  fof(f5,axiom,(
% 1.36/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.36/0.56  fof(f217,plain,(
% 1.36/0.56    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(superposition,[],[f73,f215])).
% 1.36/0.56  fof(f215,plain,(
% 1.36/0.56    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f214,f137])).
% 1.36/0.56  fof(f214,plain,(
% 1.36/0.56    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f213,f138])).
% 1.36/0.56  fof(f213,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f212,f139])).
% 1.36/0.56  fof(f212,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(sK2,k2_funct_1(sK2))) )),
% 1.36/0.56    inference(subsumption_resolution,[],[f210,f51])).
% 1.36/0.56  fof(f210,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(sK2,k2_funct_1(sK2))) )),
% 1.36/0.56    inference(resolution,[],[f84,f55])).
% 1.36/0.56  fof(f84,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f48])).
% 1.36/0.56  fof(f73,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f36])).
% 1.36/0.56  fof(f36,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.56    inference(flattening,[],[f35])).
% 1.36/0.56  fof(f35,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f6])).
% 1.36/0.56  fof(f6,axiom,(
% 1.36/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.36/0.56  fof(f375,plain,(
% 1.36/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(superposition,[],[f197,f374])).
% 1.36/0.56  fof(f374,plain,(
% 1.36/0.56    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f373,f182])).
% 1.36/0.56  fof(f182,plain,(
% 1.36/0.56    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.36/0.56    inference(forward_demodulation,[],[f171,f113])).
% 1.36/0.56  fof(f171,plain,(
% 1.36/0.56    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f166,f78])).
% 1.36/0.56  fof(f373,plain,(
% 1.36/0.56    k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f372,f158])).
% 1.36/0.56  fof(f158,plain,(
% 1.36/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f157,f137])).
% 1.36/0.56  fof(f157,plain,(
% 1.36/0.56    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f156,f55])).
% 1.36/0.56  fof(f156,plain,(
% 1.36/0.56    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f155,f51])).
% 1.36/0.56  fof(f155,plain,(
% 1.36/0.56    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f154,f138])).
% 1.36/0.56  fof(f154,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f81,f139])).
% 1.36/0.56  fof(f81,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f44])).
% 1.36/0.56  fof(f372,plain,(
% 1.36/0.56    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.36/0.56    inference(resolution,[],[f234,f166])).
% 1.36/0.56  fof(f234,plain,(
% 1.36/0.56    ( ! [X4,X3] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(k2_funct_1(sK2),X3,X4) | k1_xboole_0 = k2_relat_1(sK2) | k2_relset_1(X3,X4,k2_funct_1(sK2)) != X4 | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X3,X4,k2_funct_1(sK2))) )),
% 1.36/0.56    inference(subsumption_resolution,[],[f229,f153])).
% 1.36/0.56  fof(f229,plain,(
% 1.36/0.56    ( ! [X4,X3] : (k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),X3,X4) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_relset_1(X3,X4,k2_funct_1(sK2)) != X4 | ~v1_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X3,X4,k2_funct_1(sK2))) )),
% 1.36/0.56    inference(resolution,[],[f224,f83])).
% 1.36/0.56  fof(f83,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f46])).
% 1.36/0.56  fof(f46,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.56    inference(flattening,[],[f45])).
% 1.36/0.56  fof(f45,plain,(
% 1.36/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f19])).
% 1.36/0.56  fof(f19,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.36/0.56  fof(f197,plain,(
% 1.36/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f140,f196])).
% 1.36/0.56  fof(f196,plain,(
% 1.36/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f195,f137])).
% 1.36/0.56  fof(f195,plain,(
% 1.36/0.56    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.36/0.56    inference(subsumption_resolution,[],[f194,f138])).
% 1.36/0.56  fof(f194,plain,(
% 1.36/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.36/0.56    inference(resolution,[],[f193,f139])).
% 1.36/0.56  fof(f193,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) )),
% 1.36/0.56    inference(subsumption_resolution,[],[f191,f51])).
% 1.36/0.56  fof(f191,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) )),
% 1.36/0.56    inference(resolution,[],[f83,f55])).
% 1.36/0.56  fof(f140,plain,(
% 1.36/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f122,f134])).
% 1.36/0.56  fof(f122,plain,(
% 1.36/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f97,f118])).
% 1.36/0.56  fof(f97,plain,(
% 1.36/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f96,f92])).
% 1.36/0.56  fof(f96,plain,(
% 1.36/0.56    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.36/0.56    inference(backward_demodulation,[],[f56,f91])).
% 1.36/0.56  fof(f56,plain,(
% 1.36/0.56    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f126,plain,(
% 1.36/0.56    ~v1_xboole_0(k2_relat_1(sK2))),
% 1.36/0.56    inference(subsumption_resolution,[],[f125,f57])).
% 1.36/0.56  fof(f57,plain,(
% 1.36/0.56    ~v2_struct_0(sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f24])).
% 1.36/0.56  fof(f125,plain,(
% 1.36/0.56    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1)),
% 1.36/0.56    inference(subsumption_resolution,[],[f124,f58])).
% 1.36/0.56  fof(f124,plain,(
% 1.36/0.56    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.36/0.56    inference(superposition,[],[f66,f118])).
% 1.36/0.56  fof(f66,plain,(
% 1.36/0.56    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f28])).
% 1.36/0.56  fof(f28,plain,(
% 1.36/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.36/0.56    inference(flattening,[],[f27])).
% 1.36/0.56  fof(f27,plain,(
% 1.36/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f18])).
% 1.36/0.56  fof(f18,axiom,(
% 1.36/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.36/0.56  % SZS output end Proof for theBenchmark
% 1.36/0.56  % (1471)------------------------------
% 1.36/0.56  % (1471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (1471)Termination reason: Refutation
% 1.36/0.56  
% 1.36/0.56  % (1471)Memory used [KB]: 6524
% 1.36/0.56  % (1471)Time elapsed: 0.126 s
% 1.36/0.56  % (1471)------------------------------
% 1.36/0.56  % (1471)------------------------------
% 1.36/0.56  % (1464)Success in time 0.197 s
%------------------------------------------------------------------------------
