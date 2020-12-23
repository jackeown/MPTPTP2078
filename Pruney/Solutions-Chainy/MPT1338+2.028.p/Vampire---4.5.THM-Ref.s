%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  159 (1978 expanded)
%              Number of leaves         :   20 ( 389 expanded)
%              Depth                    :   24
%              Number of atoms          :  441 (10107 expanded)
%              Number of equality atoms :  169 (3058 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f631,plain,(
    $false ),
    inference(subsumption_resolution,[],[f598,f58])).

% (17639)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f598,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f207,f575])).

fof(f575,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f574,f465])).

fof(f465,plain,
    ( k2_relat_1(sK2) != k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f464,f210])).

fof(f210,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f201,f109])).

fof(f109,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f108,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f108,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f97])).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f93,f90])).

fof(f90,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f62,f57])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
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
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

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
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
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
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f52,f89])).

fof(f89,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f201,plain,(
    k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    inference(resolution,[],[f75,f135])).

fof(f135,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f134,f110])).

fof(f110,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f108,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f134,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f133,f109])).

% (17643)Refutation not found, incomplete strategy% (17643)------------------------------
% (17643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17643)Termination reason: Refutation not found, incomplete strategy

% (17643)Memory used [KB]: 10618
% (17643)Time elapsed: 0.146 s
% (17643)------------------------------
% (17643)------------------------------
fof(f133,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(subsumption_resolution,[],[f131,f130])).

fof(f130,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f129,f108])).

fof(f129,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f126,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f126,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f69,f120])).

fof(f120,plain,(
    k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f119,f108])).

fof(f119,plain,
    ( ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f118,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f131,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(resolution,[],[f128,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f128,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f127,f108])).

fof(f127,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f125,f50])).

fof(f125,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f70,f120])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f464,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | k2_relat_1(sK2) != k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f463,f461])).

fof(f461,plain,(
    k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f460,f200])).

fof(f200,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f75,f123])).

fof(f123,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f121,f108])).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(resolution,[],[f68,f50])).

fof(f460,plain,
    ( k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f458,f114])).

fof(f114,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f112,f108])).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(resolution,[],[f67,f50])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f458,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f457,f123])).

fof(f457,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2)
      | k2_relset_1(X0,X1,sK2) != X1 ) ),
    inference(forward_demodulation,[],[f456,f120])).

fof(f456,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) ) ),
    inference(subsumption_resolution,[],[f455,f50])).

fof(f455,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v1_funct_1(sK2)
      | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) ) ),
    inference(resolution,[],[f79,f54])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f463,plain,
    ( k2_relat_1(sK2) != k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f462,f315])).

fof(f315,plain,(
    k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f311,f261])).

fof(f261,plain,(
    ! [X2] : k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X2) = k10_relat_1(k4_relat_1(sK2),X2) ),
    inference(resolution,[],[f84,f135])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f311,plain,(
    k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    inference(resolution,[],[f78,f135])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f462,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f403,f461])).

fof(f403,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f209,f357])).

fof(f357,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f356,f108])).

fof(f356,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f355,f111])).

fof(f111,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f76,f97])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f355,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f353,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f353,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f351,f205])).

fof(f205,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f98,f202])).

fof(f202,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f96,f199])).

fof(f199,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f75,f97])).

fof(f96,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f94,f90])).

fof(f94,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f53,f89])).

fof(f53,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f92,f90])).

fof(f92,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f51,f89])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f351,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f347,f204])).

fof(f204,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f97,f202])).

fof(f347,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k1_xboole_0 = X1
      | v1_partfun1(sK2,X0) ) ),
    inference(resolution,[],[f82,f50])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f209,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f206,f202])).

fof(f206,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f100,f202])).

fof(f100,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f99,f90])).

fof(f99,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f95,f90])).

fof(f95,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f91,f89])).

fof(f91,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f49,f89])).

fof(f49,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f574,plain,
    ( k2_relat_1(sK2) = k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f573,f86])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f573,plain,
    ( k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relat_1(k6_partfun1(k2_relat_1(sK2)))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f175,f571])).

fof(f571,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f570,f200])).

fof(f570,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f568,f114])).

fof(f568,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f567,f123])).

fof(f567,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k6_partfun1(X1) = k5_relat_1(k4_relat_1(sK2),sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f566,f120])).

fof(f566,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2) ) ),
    inference(subsumption_resolution,[],[f565,f50])).

fof(f565,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2) ) ),
    inference(resolution,[],[f81,f54])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f175,plain,(
    k1_relat_1(k5_relat_1(k4_relat_1(sK2),sK2)) = k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f170,f130])).

fof(f170,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k5_relat_1(X2,sK2)) = k10_relat_1(X2,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f65,f108])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f207,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f104,f202])).

fof(f104,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f103,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f101,f56])).

% (17637)Refutation not found, incomplete strategy% (17637)------------------------------
% (17637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17637)Termination reason: Refutation not found, incomplete strategy

% (17637)Memory used [KB]: 10746
% (17637)Time elapsed: 0.145 s
% (17637)------------------------------
% (17637)------------------------------
fof(f101,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f66,f89])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17632)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (17640)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (17629)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (17648)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (17631)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (17635)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (17634)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (17637)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (17628)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (17655)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (17654)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (17644)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (17653)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (17627)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (17647)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (17632)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (17626)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (17648)Refutation not found, incomplete strategy% (17648)------------------------------
% 0.22/0.55  % (17648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17648)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17648)Memory used [KB]: 11129
% 0.22/0.55  % (17648)Time elapsed: 0.130 s
% 0.22/0.55  % (17648)------------------------------
% 0.22/0.55  % (17648)------------------------------
% 0.22/0.55  % (17630)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (17652)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (17643)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (17645)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f631,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f598,f58])).
% 0.22/0.56  % (17639)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.56  fof(f598,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f207,f575])).
% 0.22/0.56  fof(f575,plain,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f574,f465])).
% 0.22/0.56  fof(f465,plain,(
% 0.22/0.56    k2_relat_1(sK2) != k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f464,f210])).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f201,f109])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.22/0.56    inference(resolution,[],[f108,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    v1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f74,f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.56    inference(backward_demodulation,[],[f93,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f62,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    l1_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f20])).
% 0.22/0.56  fof(f20,conjecture,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.56    inference(backward_demodulation,[],[f52,f89])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.56    inference(resolution,[],[f62,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    l1_struct_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.22/0.56    inference(resolution,[],[f75,f135])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.56    inference(forward_demodulation,[],[f134,f110])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.22/0.56    inference(resolution,[],[f108,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))))),
% 0.22/0.56    inference(forward_demodulation,[],[f133,f109])).
% 0.22/0.56  % (17643)Refutation not found, incomplete strategy% (17643)------------------------------
% 0.22/0.56  % (17643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17643)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (17643)Memory used [KB]: 10618
% 0.22/0.56  % (17643)Time elapsed: 0.146 s
% 0.22/0.56  % (17643)------------------------------
% 0.22/0.56  % (17643)------------------------------
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f131,f130])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    v1_relat_1(k4_relat_1(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f129,f108])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f126,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f69,f120])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    k4_relat_1(sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f119,f108])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f118,f50])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f71,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    v2_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    ~v1_relat_1(k4_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 0.22/0.56    inference(resolution,[],[f128,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    v1_funct_1(k4_relat_1(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f127,f108])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f125,f50])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f70,f120])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f464,plain,(
% 0.22/0.56    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | k2_relat_1(sK2) != k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f463,f461])).
% 0.22/0.56  fof(f461,plain,(
% 0.22/0.56    k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f460,f200])).
% 0.22/0.56  fof(f200,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.56    inference(resolution,[],[f75,f123])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f121,f108])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.56    inference(resolution,[],[f68,f50])).
% 0.22/0.56  fof(f460,plain,(
% 0.22/0.56    k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f458,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f112,f108])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.56    inference(resolution,[],[f67,f50])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f458,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.56    inference(resolution,[],[f457,f123])).
% 0.22/0.56  fof(f457,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) )),
% 0.22/0.56    inference(forward_demodulation,[],[f456,f120])).
% 0.22/0.56  fof(f456,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f455,f50])).
% 0.22/0.56  fof(f455,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) )),
% 0.22/0.56    inference(resolution,[],[f79,f54])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.56  fof(f463,plain,(
% 0.22/0.56    k2_relat_1(sK2) != k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f462,f315])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f311,f261])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    ( ! [X2] : (k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),X2) = k10_relat_1(k4_relat_1(sK2),X2)) )),
% 0.22/0.56    inference(resolution,[],[f84,f135])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.56  fof(f311,plain,(
% 0.22/0.56    k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.22/0.56    inference(resolution,[],[f78,f135])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.56  fof(f462,plain,(
% 0.22/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f403,f461])).
% 0.22/0.56  fof(f403,plain,(
% 0.22/0.56    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f209,f357])).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f356,f108])).
% 0.22/0.56  fof(f356,plain,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f355,f111])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f76,f97])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f353,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.56  fof(f353,plain,(
% 0.22/0.56    v1_partfun1(sK2,k2_struct_0(sK0)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f351,f205])).
% 0.22/0.56  fof(f205,plain,(
% 0.22/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f98,f202])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f96,f199])).
% 0.22/0.56  fof(f199,plain,(
% 0.22/0.56    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f75,f97])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f94,f90])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f53,f89])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f92,f90])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f51,f89])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f351,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f347,f204])).
% 0.22/0.56  fof(f204,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.56    inference(backward_demodulation,[],[f97,f202])).
% 0.22/0.56  fof(f347,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | v1_partfun1(sK2,X0)) )),
% 0.22/0.56    inference(resolution,[],[f82,f50])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.56  fof(f209,plain,(
% 0.22/0.56    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f206,f202])).
% 0.22/0.56  fof(f206,plain,(
% 0.22/0.56    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f100,f202])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f99,f90])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f95,f90])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f91,f89])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f49,f89])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f574,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f573,f86])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f60,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.56  fof(f573,plain,(
% 0.22/0.56    k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2)) = k1_relat_1(k6_partfun1(k2_relat_1(sK2))) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f175,f571])).
% 0.22/0.56  fof(f571,plain,(
% 0.22/0.56    k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f570,f200])).
% 0.22/0.56  fof(f570,plain,(
% 0.22/0.56    k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f568,f114])).
% 0.22/0.56  fof(f568,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f567,f123])).
% 0.22/0.56  fof(f567,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k6_partfun1(X1) = k5_relat_1(k4_relat_1(sK2),sK2) | k2_relset_1(X0,X1,sK2) != X1 | k1_xboole_0 = X1) )),
% 0.22/0.56    inference(forward_demodulation,[],[f566,f120])).
% 0.22/0.56  fof(f566,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f565,f50])).
% 0.22/0.56  fof(f565,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(sK2),sK2)) )),
% 0.22/0.56    inference(resolution,[],[f81,f54])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    k1_relat_1(k5_relat_1(k4_relat_1(sK2),sK2)) = k10_relat_1(k4_relat_1(sK2),k1_relat_1(sK2))),
% 0.22/0.56    inference(resolution,[],[f170,f130])).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    ( ! [X2] : (~v1_relat_1(X2) | k1_relat_1(k5_relat_1(X2,sK2)) = k10_relat_1(X2,k1_relat_1(sK2))) )),
% 0.22/0.56    inference(resolution,[],[f65,f108])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f104,f202])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f103,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ~v2_struct_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f101,f56])).
% 0.22/0.56  % (17637)Refutation not found, incomplete strategy% (17637)------------------------------
% 0.22/0.56  % (17637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17637)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (17637)Memory used [KB]: 10746
% 0.22/0.56  % (17637)Time elapsed: 0.145 s
% 0.22/0.56  % (17637)------------------------------
% 0.22/0.56  % (17637)------------------------------
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.22/0.56    inference(superposition,[],[f66,f89])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (17632)------------------------------
% 0.22/0.56  % (17632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17632)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (17632)Memory used [KB]: 6908
% 0.22/0.56  % (17632)Time elapsed: 0.122 s
% 0.22/0.56  % (17632)------------------------------
% 0.22/0.56  % (17632)------------------------------
% 0.22/0.56  % (17636)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (17625)Success in time 0.198 s
%------------------------------------------------------------------------------
