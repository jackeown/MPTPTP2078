%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:32 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  148 (2046 expanded)
%              Number of leaves         :   15 ( 398 expanded)
%              Depth                    :   27
%              Number of atoms          :  453 (10072 expanded)
%              Number of equality atoms :  130 (1753 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(subsumption_resolution,[],[f295,f63])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f295,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f138,f292])).

fof(f292,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f291,f237])).

fof(f237,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f145,f156])).

fof(f156,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f155,f146])).

fof(f146,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f131,f136])).

fof(f136,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f102,f133])).

fof(f133,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f103,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f103,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f95,f99])).

fof(f99,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f47,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f47,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

% (18984)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (18990)Refutation not found, incomplete strategy% (18990)------------------------------
% (18990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18990)Termination reason: Refutation not found, incomplete strategy

% (18990)Memory used [KB]: 1791
% (18990)Time elapsed: 0.096 s
% (18990)------------------------------
% (18990)------------------------------
% (19008)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (19002)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f41,f92])).

fof(f92,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f46,f59])).

fof(f46,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f96,f99])).

fof(f96,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f42,f92])).

fof(f42,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f131,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f103,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f155,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f149,f139])).

fof(f139,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f103,f136])).

fof(f149,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(resolution,[],[f140,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f140,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f104,f136])).

fof(f104,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f94,f99])).

fof(f94,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f40,f92])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f145,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(backward_demodulation,[],[f130,f136])).

fof(f130,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f129,f103])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f110,f39])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(resolution,[],[f104,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f291,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f236,f240])).

fof(f240,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f224,f156])).

fof(f224,plain,
    ( k1_relat_1(sK2) != k2_struct_0(sK0)
    | sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f214,f218])).

fof(f218,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f202,f213])).

fof(f213,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f91,f148])).

fof(f148,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f134,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f103,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f202,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f201,f161])).

fof(f161,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f88,f148])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f82,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f201,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f195,f115])).

fof(f115,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f114,f102])).

fof(f114,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f113,f43])).

fof(f113,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f112,f103])).

fof(f112,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f106,f39])).

fof(f106,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f104,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f195,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f194,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f194,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f90,f148])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f84,f39])).

fof(f84,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f214,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f190,f213])).

fof(f190,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f180,f188])).

fof(f188,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f142,f60])).

fof(f142,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f123,f136])).

fof(f123,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f122,f102])).

fof(f122,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f121,f43])).

fof(f121,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f120,f103])).

fof(f120,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f108,f39])).

fof(f108,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f104,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f180,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(global_subsumption,[],[f90,f148,f179])).

fof(f179,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f178,f142])).

fof(f178,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f166,f115])).

fof(f166,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f141,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f141,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f119,f136])).

fof(f119,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f118,f102])).

fof(f118,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f116,f103])).

fof(f116,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f107,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f104,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f236,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f144,f156])).

fof(f144,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f128,f136])).

fof(f128,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f101,f127])).

fof(f127,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f126,f43])).

fof(f126,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f125,f102])).

fof(f125,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f124,f103])).

fof(f124,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f109,f39])).

fof(f109,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f104,f50])).

fof(f101,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f97,f99])).

fof(f97,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f44,f92])).

fof(f44,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f98,f136])).

fof(f98,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:51:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (19005)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (18985)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (18986)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.42/0.55  % (18996)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (19006)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.42/0.55  % (18988)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.42/0.55  % (18989)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.42/0.56  % (18999)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.42/0.56  % (18989)Refutation not found, incomplete strategy% (18989)------------------------------
% 1.42/0.56  % (18989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (18995)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.42/0.57  % (18987)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.42/0.57  % (18988)Refutation found. Thanks to Tanya!
% 1.42/0.57  % SZS status Theorem for theBenchmark
% 1.42/0.57  % (18989)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (18989)Memory used [KB]: 10618
% 1.42/0.57  % (18989)Time elapsed: 0.120 s
% 1.42/0.57  % (18989)------------------------------
% 1.42/0.57  % (18989)------------------------------
% 1.42/0.57  % (18990)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.42/0.57  % (19003)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.42/0.57  % (18993)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.42/0.57  % (19001)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.64/0.57  % (18994)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.64/0.57  % (18997)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.64/0.57  % (19004)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f311,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(subsumption_resolution,[],[f295,f63])).
% 1.64/0.58  fof(f63,plain,(
% 1.64/0.58    v1_xboole_0(k1_xboole_0)),
% 1.64/0.58    inference(cnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    v1_xboole_0(k1_xboole_0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.64/0.58  fof(f295,plain,(
% 1.64/0.58    ~v1_xboole_0(k1_xboole_0)),
% 1.64/0.58    inference(backward_demodulation,[],[f138,f292])).
% 1.64/0.58  fof(f292,plain,(
% 1.64/0.58    k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.58    inference(subsumption_resolution,[],[f291,f237])).
% 1.64/0.58  fof(f237,plain,(
% 1.64/0.58    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.58    inference(superposition,[],[f145,f156])).
% 1.64/0.58  fof(f156,plain,(
% 1.64/0.58    k1_relat_1(sK2) = k2_struct_0(sK0) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.58    inference(forward_demodulation,[],[f155,f146])).
% 1.64/0.58  fof(f146,plain,(
% 1.64/0.58    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.64/0.58    inference(backward_demodulation,[],[f131,f136])).
% 1.64/0.58  fof(f136,plain,(
% 1.64/0.58    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.64/0.58    inference(backward_demodulation,[],[f102,f133])).
% 1.64/0.58  fof(f133,plain,(
% 1.64/0.58    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.58    inference(resolution,[],[f103,f60])).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f32])).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.58    inference(ennf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.64/0.58  fof(f103,plain,(
% 1.64/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.64/0.58    inference(backward_demodulation,[],[f95,f99])).
% 1.64/0.58  fof(f99,plain,(
% 1.64/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.64/0.58    inference(resolution,[],[f47,f59])).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f31])).
% 1.64/0.58  fof(f31,plain,(
% 1.64/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f12])).
% 1.64/0.58  fof(f12,axiom,(
% 1.64/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.64/0.58  fof(f47,plain,(
% 1.64/0.58    l1_struct_0(sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f18])).
% 1.64/0.58  fof(f18,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.64/0.58    inference(flattening,[],[f17])).
% 1.64/0.58  fof(f17,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,negated_conjecture,(
% 1.64/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.64/0.58    inference(negated_conjecture,[],[f15])).
% 1.64/0.58  fof(f15,conjecture,(
% 1.64/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 1.64/0.58  % (18984)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.59  % (18990)Refutation not found, incomplete strategy% (18990)------------------------------
% 1.64/0.59  % (18990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (18990)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (18990)Memory used [KB]: 1791
% 1.64/0.59  % (18990)Time elapsed: 0.096 s
% 1.64/0.59  % (18990)------------------------------
% 1.64/0.59  % (18990)------------------------------
% 1.64/0.59  % (19008)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.64/0.59  % (19002)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.64/0.59  fof(f95,plain,(
% 1.64/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.64/0.59    inference(backward_demodulation,[],[f41,f92])).
% 1.64/0.59  fof(f92,plain,(
% 1.64/0.59    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.64/0.59    inference(resolution,[],[f46,f59])).
% 1.64/0.59  fof(f46,plain,(
% 1.64/0.59    l1_struct_0(sK1)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f41,plain,(
% 1.64/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f102,plain,(
% 1.64/0.59    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(backward_demodulation,[],[f96,f99])).
% 1.64/0.59  fof(f96,plain,(
% 1.64/0.59    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(backward_demodulation,[],[f42,f92])).
% 1.64/0.59  fof(f42,plain,(
% 1.64/0.59    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f131,plain,(
% 1.64/0.59    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(resolution,[],[f103,f72])).
% 1.64/0.59  fof(f72,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f38])).
% 1.64/0.59  fof(f38,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(ennf_transformation,[],[f7])).
% 1.64/0.59  fof(f7,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.64/0.59  fof(f155,plain,(
% 1.64/0.59    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f149,f139])).
% 1.64/0.59  fof(f139,plain,(
% 1.64/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.64/0.59    inference(backward_demodulation,[],[f103,f136])).
% 1.64/0.59  fof(f149,plain,(
% 1.64/0.59    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.64/0.59    inference(resolution,[],[f140,f71])).
% 1.64/0.59  fof(f71,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f37])).
% 1.64/0.59  fof(f37,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(flattening,[],[f36])).
% 1.64/0.59  fof(f36,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(ennf_transformation,[],[f9])).
% 1.64/0.59  fof(f9,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.64/0.59  fof(f140,plain,(
% 1.64/0.59    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.64/0.59    inference(backward_demodulation,[],[f104,f136])).
% 1.64/0.59  fof(f104,plain,(
% 1.64/0.59    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.64/0.59    inference(backward_demodulation,[],[f94,f99])).
% 1.64/0.59  fof(f94,plain,(
% 1.64/0.59    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 1.64/0.59    inference(backward_demodulation,[],[f40,f92])).
% 1.64/0.59  fof(f40,plain,(
% 1.64/0.59    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f145,plain,(
% 1.64/0.59    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.64/0.59    inference(backward_demodulation,[],[f130,f136])).
% 1.64/0.59  fof(f130,plain,(
% 1.64/0.59    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f129,f103])).
% 1.64/0.59  fof(f129,plain,(
% 1.64/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f110,f39])).
% 1.64/0.59  fof(f39,plain,(
% 1.64/0.59    v1_funct_1(sK2)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f110,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.64/0.59    inference(resolution,[],[f104,f79])).
% 1.64/0.59  fof(f79,plain,(
% 1.64/0.59    ( ! [X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f73])).
% 1.64/0.59  fof(f73,plain,(
% 1.64/0.59    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.64/0.59    inference(equality_resolution,[],[f48])).
% 1.64/0.59  fof(f48,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.64/0.59    inference(flattening,[],[f19])).
% 1.64/0.59  fof(f19,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.64/0.59    inference(ennf_transformation,[],[f10])).
% 1.64/0.59  fof(f10,axiom,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.64/0.59  fof(f291,plain,(
% 1.64/0.59    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f290])).
% 1.64/0.59  fof(f290,plain,(
% 1.64/0.59    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.59    inference(superposition,[],[f236,f240])).
% 1.64/0.59  fof(f240,plain,(
% 1.64/0.59    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.59    inference(trivial_inequality_removal,[],[f239])).
% 1.64/0.59  fof(f239,plain,(
% 1.64/0.59    k1_relat_1(sK2) != k1_relat_1(sK2) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.59    inference(superposition,[],[f224,f156])).
% 1.64/0.59  fof(f224,plain,(
% 1.64/0.59    k1_relat_1(sK2) != k2_struct_0(sK0) | sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.64/0.59    inference(backward_demodulation,[],[f214,f218])).
% 1.64/0.59  fof(f218,plain,(
% 1.64/0.59    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(backward_demodulation,[],[f202,f213])).
% 1.64/0.59  fof(f213,plain,(
% 1.64/0.59    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f91,f148])).
% 1.64/0.59  fof(f148,plain,(
% 1.64/0.59    v1_relat_1(sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f134,f62])).
% 1.64/0.59  fof(f62,plain,(
% 1.64/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f3])).
% 1.64/0.59  fof(f3,axiom,(
% 1.64/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.64/0.59  fof(f134,plain,(
% 1.64/0.59    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2)),
% 1.64/0.59    inference(resolution,[],[f103,f61])).
% 1.64/0.59  fof(f61,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f33])).
% 1.64/0.59  fof(f33,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f2])).
% 1.64/0.59  fof(f2,axiom,(
% 1.64/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.64/0.59  fof(f91,plain,(
% 1.64/0.59    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f85,f39])).
% 1.64/0.59  fof(f85,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f43,f54])).
% 1.64/0.59  fof(f54,plain,(
% 1.64/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f26])).
% 1.64/0.59  fof(f26,plain,(
% 1.64/0.59    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(flattening,[],[f25])).
% 1.64/0.59  fof(f25,plain,(
% 1.64/0.59    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f6])).
% 1.64/0.59  fof(f6,axiom,(
% 1.64/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.64/0.59  fof(f43,plain,(
% 1.64/0.59    v2_funct_1(sK2)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f202,plain,(
% 1.64/0.59    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 1.64/0.59    inference(subsumption_resolution,[],[f201,f161])).
% 1.64/0.59  fof(f161,plain,(
% 1.64/0.59    v1_relat_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f88,f148])).
% 1.64/0.59  fof(f88,plain,(
% 1.64/0.59    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f82,f39])).
% 1.64/0.59  fof(f82,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f43,f55])).
% 1.64/0.59  fof(f55,plain,(
% 1.64/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f28])).
% 1.64/0.59  fof(f28,plain,(
% 1.64/0.59    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(flattening,[],[f27])).
% 1.64/0.59  fof(f27,plain,(
% 1.64/0.59    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f4])).
% 1.64/0.59  fof(f4,axiom,(
% 1.64/0.59    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.64/0.59  fof(f201,plain,(
% 1.64/0.59    ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 1.64/0.59    inference(subsumption_resolution,[],[f195,f115])).
% 1.64/0.59  fof(f115,plain,(
% 1.64/0.59    v1_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f114,f102])).
% 1.64/0.59  fof(f114,plain,(
% 1.64/0.59    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f113,f43])).
% 1.64/0.59  fof(f113,plain,(
% 1.64/0.59    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f112,f103])).
% 1.64/0.59  fof(f112,plain,(
% 1.64/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f106,f39])).
% 1.64/0.59  fof(f106,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f104,f51])).
% 1.64/0.59  fof(f51,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f24])).
% 1.64/0.59  fof(f24,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.64/0.59    inference(flattening,[],[f23])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.64/0.59    inference(ennf_transformation,[],[f11])).
% 1.64/0.59  fof(f11,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.64/0.59  fof(f195,plain,(
% 1.64/0.59    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 1.64/0.59    inference(resolution,[],[f194,f64])).
% 1.64/0.59  fof(f64,plain,(
% 1.64/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f35])).
% 1.64/0.59  fof(f35,plain,(
% 1.64/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(flattening,[],[f34])).
% 1.64/0.59  fof(f34,plain,(
% 1.64/0.59    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f5])).
% 1.64/0.59  fof(f5,axiom,(
% 1.64/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.64/0.59  fof(f194,plain,(
% 1.64/0.59    v2_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f90,f148])).
% 1.64/0.59  fof(f90,plain,(
% 1.64/0.59    ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f84,f39])).
% 1.64/0.59  fof(f84,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f43,f57])).
% 1.64/0.59  fof(f57,plain,(
% 1.64/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f28])).
% 1.64/0.59  fof(f214,plain,(
% 1.64/0.59    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0)),
% 1.64/0.59    inference(backward_demodulation,[],[f190,f213])).
% 1.64/0.59  fof(f190,plain,(
% 1.64/0.59    k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.64/0.59    inference(backward_demodulation,[],[f180,f188])).
% 1.64/0.59  fof(f188,plain,(
% 1.64/0.59    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f142,f60])).
% 1.64/0.59  fof(f142,plain,(
% 1.64/0.59    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.64/0.59    inference(backward_demodulation,[],[f123,f136])).
% 1.64/0.59  fof(f123,plain,(
% 1.64/0.59    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.64/0.59    inference(subsumption_resolution,[],[f122,f102])).
% 1.64/0.59  fof(f122,plain,(
% 1.64/0.59    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.64/0.59    inference(subsumption_resolution,[],[f121,f43])).
% 1.64/0.59  fof(f121,plain,(
% 1.64/0.59    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.64/0.59    inference(subsumption_resolution,[],[f120,f103])).
% 1.64/0.59  fof(f120,plain,(
% 1.64/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.64/0.59    inference(subsumption_resolution,[],[f108,f39])).
% 1.64/0.59  fof(f108,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.64/0.59    inference(resolution,[],[f104,f53])).
% 1.64/0.59  fof(f53,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f24])).
% 1.64/0.59  fof(f180,plain,(
% 1.64/0.59    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.64/0.59    inference(global_subsumption,[],[f90,f148,f179])).
% 1.64/0.59  fof(f179,plain,(
% 1.64/0.59    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f178,f142])).
% 1.64/0.59  fof(f178,plain,(
% 1.64/0.59    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.64/0.59    inference(subsumption_resolution,[],[f166,f115])).
% 1.64/0.59  fof(f166,plain,(
% 1.64/0.59    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.64/0.59    inference(resolution,[],[f141,f50])).
% 1.64/0.59  fof(f50,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f22])).
% 1.64/0.59  fof(f22,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.64/0.59    inference(flattening,[],[f21])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.64/0.59    inference(ennf_transformation,[],[f14])).
% 1.64/0.59  fof(f14,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.64/0.59  fof(f141,plain,(
% 1.64/0.59    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.64/0.59    inference(backward_demodulation,[],[f119,f136])).
% 1.64/0.59  fof(f119,plain,(
% 1.64/0.59    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.64/0.59    inference(subsumption_resolution,[],[f118,f102])).
% 1.64/0.59  fof(f118,plain,(
% 1.64/0.59    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.64/0.59    inference(subsumption_resolution,[],[f117,f43])).
% 1.64/0.59  fof(f117,plain,(
% 1.64/0.59    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.64/0.59    inference(subsumption_resolution,[],[f116,f103])).
% 1.64/0.59  fof(f116,plain,(
% 1.64/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.64/0.59    inference(subsumption_resolution,[],[f107,f39])).
% 1.64/0.59  fof(f107,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.64/0.59    inference(resolution,[],[f104,f52])).
% 1.64/0.59  fof(f52,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f24])).
% 1.64/0.59  fof(f236,plain,(
% 1.64/0.59    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.64/0.59    inference(superposition,[],[f144,f156])).
% 1.64/0.59  fof(f144,plain,(
% 1.64/0.59    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 1.64/0.59    inference(backward_demodulation,[],[f128,f136])).
% 1.64/0.59  fof(f128,plain,(
% 1.64/0.59    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 1.64/0.59    inference(backward_demodulation,[],[f101,f127])).
% 1.64/0.59  fof(f127,plain,(
% 1.64/0.59    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f126,f43])).
% 1.64/0.59  fof(f126,plain,(
% 1.64/0.59    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f125,f102])).
% 1.64/0.59  fof(f125,plain,(
% 1.64/0.59    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f124,f103])).
% 1.64/0.59  fof(f124,plain,(
% 1.64/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(subsumption_resolution,[],[f109,f39])).
% 1.64/0.59  fof(f109,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.64/0.59    inference(resolution,[],[f104,f50])).
% 1.64/0.59  fof(f101,plain,(
% 1.64/0.59    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.64/0.59    inference(backward_demodulation,[],[f97,f99])).
% 1.64/0.59  fof(f97,plain,(
% 1.64/0.59    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.64/0.59    inference(backward_demodulation,[],[f44,f92])).
% 1.64/0.59  fof(f44,plain,(
% 1.64/0.59    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f138,plain,(
% 1.64/0.59    ~v1_xboole_0(k2_relat_1(sK2))),
% 1.64/0.59    inference(backward_demodulation,[],[f98,f136])).
% 1.64/0.59  fof(f98,plain,(
% 1.64/0.59    ~v1_xboole_0(k2_struct_0(sK1))),
% 1.64/0.59    inference(subsumption_resolution,[],[f93,f45])).
% 1.64/0.59  fof(f45,plain,(
% 1.64/0.59    ~v2_struct_0(sK1)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f93,plain,(
% 1.64/0.59    v2_struct_0(sK1) | ~v1_xboole_0(k2_struct_0(sK1))),
% 1.64/0.59    inference(resolution,[],[f46,f58])).
% 1.64/0.59  fof(f58,plain,(
% 1.64/0.59    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f30])).
% 1.64/0.59  fof(f30,plain,(
% 1.64/0.59    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.64/0.59    inference(flattening,[],[f29])).
% 1.64/0.59  fof(f29,plain,(
% 1.64/0.59    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f13])).
% 1.64/0.59  fof(f13,axiom,(
% 1.64/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.64/0.59  % SZS output end Proof for theBenchmark
% 1.64/0.59  % (18988)------------------------------
% 1.64/0.59  % (18988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (18988)Termination reason: Refutation
% 1.64/0.59  
% 1.64/0.59  % (18988)Memory used [KB]: 6268
% 1.64/0.59  % (18988)Time elapsed: 0.135 s
% 1.64/0.59  % (18988)------------------------------
% 1.64/0.59  % (18988)------------------------------
% 1.64/0.59  % (18982)Success in time 0.225 s
%------------------------------------------------------------------------------
