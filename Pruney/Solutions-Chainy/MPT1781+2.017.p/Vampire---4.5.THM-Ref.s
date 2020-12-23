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
% DateTime   : Thu Dec  3 13:19:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  377 (796432172 expanded)
%              Number of leaves         :   12 (145929868 expanded)
%              Depth                    :  106
%              Number of atoms          : 1500 (5865672029 expanded)
%              Number of equality atoms :  516 (752051726 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1369,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1342,f1097])).

fof(f1097,plain,(
    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1028,f1086])).

fof(f1086,plain,(
    k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f1030,f1028])).

fof(f1030,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(backward_demodulation,[],[f572,f1021])).

fof(f1021,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f943,f532])).

fof(f532,plain,(
    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f99,f523])).

fof(f523,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f446,f99])).

fof(f446,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f35,f435])).

fof(f435,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f429,f434])).

fof(f434,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f433,f269])).

fof(f269,plain,
    ( k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f268,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f268,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f106])).

fof(f106,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f104,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f104,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f34,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f260,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f185,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f185,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f115])).

fof(f115,plain,(
    v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f114,f53])).

fof(f114,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f94,f52])).

fof(f94,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f92,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f78,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f184,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f88])).

fof(f88,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f76,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f37,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f174,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f48,f168])).

fof(f168,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f127,f134])).

fof(f134,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f109,f105])).

fof(f105,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f97,f103])).

fof(f103,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f34,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f97,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) ),
    inference(subsumption_resolution,[],[f95,f34])).

fof(f95,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f33,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f33,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f107,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f91,f64])).

fof(f91,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f90,f38])).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f127,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f113,f105])).

fof(f113,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f94,f55])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
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
         => ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(f433,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f432,f88])).

fof(f432,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f431,f115])).

fof(f431,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f424,f241])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f240,f106])).

fof(f240,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f238,f32])).

fof(f238,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f237,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f237,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f32])).

fof(f236,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f230,f106])).

fof(f230,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f181,f67])).

fof(f181,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f115])).

fof(f180,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f88])).

fof(f172,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f47,f168])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f424,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f423,f276])).

fof(f276,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f275,f217])).

fof(f217,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f106])).

fof(f216,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f32])).

fof(f210,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f179,f67])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f88])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f115])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f47,f168])).

fof(f275,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f271,f105])).

fof(f271,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f247,f31])).

fof(f31,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f247,plain,
    ( m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f227,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_relat_1(sK2))
      | m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f81,f105])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f80,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f74,f40])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f227,plain,
    ( m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f217,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f423,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f422])).

fof(f422,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f257,f364])).

fof(f364,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f357,f363])).

fof(f363,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f362,f269])).

fof(f362,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f361,f88])).

fof(f361,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f360,f115])).

fof(f360,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f341,f241])).

fof(f341,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f340,f217])).

fof(f340,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f270,f105])).

fof(f270,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f247,f85])).

fof(f85,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f84,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f83,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f82,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f75,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f357,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f341,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f257,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f256,f106])).

fof(f256,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f32])).

fof(f248,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f183,f67])).

fof(f183,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f88])).

fof(f182,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f115])).

fof(f173,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f48,f168])).

fof(f429,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f427])).

fof(f427,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f424,f58])).

fof(f35,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f98,f34])).

fof(f98,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f96,f32])).

fof(f96,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(resolution,[],[f33,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f943,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f527,f910])).

fof(f910,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f907,f900])).

fof(f900,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f898,f741])).

fof(f741,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f740,f669])).

fof(f669,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f668,f115])).

fof(f668,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f667,f88])).

fof(f667,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f665,f67])).

fof(f665,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f664])).

fof(f664,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f608,f639])).

fof(f639,plain,
    ( k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f636])).

fof(f636,plain,
    ( k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f576,f589])).

fof(f589,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f584,f558])).

fof(f558,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f531,f540])).

fof(f540,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f537,f526])).

fof(f526,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f34,f523])).

fof(f537,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(resolution,[],[f525,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f525,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f523])).

fof(f531,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f94,f523])).

fof(f584,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f557,f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f557,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f530,f540])).

fof(f530,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f91,f523])).

fof(f576,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f535,f540])).

fof(f535,plain,(
    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f113,f523])).

fof(f608,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f607,f32])).

fof(f607,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f601,f106])).

fof(f601,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f47,f599])).

fof(f599,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f596])).

fof(f596,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f569,f565])).

fof(f565,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f560,f554])).

fof(f554,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f526,f540])).

fof(f560,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f553,f68])).

fof(f553,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f525,f540])).

fof(f569,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f533,f540])).

fof(f533,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f103,f523])).

fof(f740,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f739])).

fof(f739,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f690,f540])).

fof(f690,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f675,f524])).

fof(f524,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_xboole_0)
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(backward_demodulation,[],[f31,f523])).

fof(f675,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | k1_xboole_0 = sK2
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f669,f51])).

fof(f898,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f897])).

fof(f897,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f711,f816])).

fof(f816,plain,
    ( sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f808,f815])).

fof(f815,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f814,f703])).

fof(f703,plain,
    ( k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f702,f88])).

fof(f702,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f701,f115])).

fof(f701,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f698,f67])).

fof(f698,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f697])).

fof(f697,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f610,f639])).

fof(f610,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f609,f106])).

fof(f609,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f602,f32])).

fof(f602,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f48,f599])).

fof(f814,plain,
    ( k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f813,f106])).

fof(f813,plain,
    ( k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f812,f32])).

fof(f812,plain,
    ( k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f806])).

fof(f806,plain,
    ( k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f764,f695])).

fof(f695,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK2
      | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f692])).

fof(f692,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | k1_xboole_0 = sK2
      | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f655,f662])).

fof(f662,plain,
    ( r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f661,f88])).

fof(f661,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f660,f115])).

fof(f660,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f658,f67])).

fof(f658,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f657])).

fof(f657,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f606,f639])).

fof(f606,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f605,f106])).

fof(f605,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK3(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f600,f32])).

fof(f600,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK3(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f47,f599])).

fof(f655,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f654,f115])).

fof(f654,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f645,f88])).

fof(f645,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f49,f639])).

fof(f764,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f763,f669])).

fof(f763,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f762])).

fof(f762,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f689,f540])).

fof(f689,plain,
    ( ~ r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f675,f529])).

fof(f529,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_xboole_0)
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(backward_demodulation,[],[f85,f523])).

fof(f808,plain,
    ( k1_xboole_0 = sK2
    | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | ~ r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f764,f58])).

fof(f711,plain,
    ( k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f710,f115])).

fof(f710,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f709,f88])).

fof(f709,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f706,f67])).

fof(f706,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f705])).

fof(f705,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f612,f639])).

fof(f612,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f611,f32])).

fof(f611,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f603,f106])).

fof(f603,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f48,f599])).

fof(f907,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f903])).

fof(f903,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f884,f58])).

fof(f884,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f882,f734])).

fof(f734,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f733,f662])).

fof(f733,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f732])).

fof(f732,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f683,f540])).

fof(f683,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f670,f524])).

fof(f670,plain,
    ( m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | k1_xboole_0 = sK2
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f662,f51])).

fof(f882,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f881])).

fof(f881,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f703,f790])).

fof(f790,plain,
    ( sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f782,f789])).

fof(f789,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f788,f711])).

fof(f788,plain,
    ( k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f787,f88])).

fof(f787,plain,
    ( k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f786,f115])).

fof(f786,plain,
    ( k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f780])).

fof(f780,plain,
    ( k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f745,f677])).

fof(f677,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f674])).

fof(f674,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = sK2
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f669,f614])).

fof(f614,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f613,f106])).

fof(f613,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f604,f32])).

fof(f604,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f49,f599])).

fof(f745,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f744,f662])).

fof(f744,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f743])).

fof(f743,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f682,f540])).

fof(f682,plain,
    ( ~ r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f670,f529])).

fof(f782,plain,
    ( k1_xboole_0 = sK2
    | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f745,f58])).

fof(f527,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f35,f523])).

fof(f572,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(superposition,[],[f527,f549])).

fof(f549,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f546,f531])).

fof(f546,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(resolution,[],[f530,f70])).

fof(f1028,plain,(
    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f532,f1021])).

fof(f1342,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1096,f1336])).

fof(f1336,plain,(
    k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1333,f1326])).

fof(f1326,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1325,f1274])).

fof(f1274,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1272,f1179])).

fof(f1179,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1168,f1100])).

fof(f1100,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | k1_funct_1(k1_xboole_0,X3) = X3 ) ),
    inference(subsumption_resolution,[],[f1093,f51])).

fof(f1093,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | k1_funct_1(k1_xboole_0,X3) = X3
      | ~ m1_subset_1(X3,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f1024,f1086])).

fof(f1024,plain,(
    ! [X3] :
      ( k1_funct_1(k1_xboole_0,X3) = X3
      | ~ m1_subset_1(X3,k1_xboole_0)
      | ~ r2_hidden(X3,u1_struct_0(sK1)) ) ),
    inference(backward_demodulation,[],[f524,f1021])).

fof(f1168,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1167,f115])).

fof(f1167,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1166,f88])).

fof(f1166,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1165,f67])).

fof(f1165,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f1135,f1121])).

fof(f1121,plain,(
    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1092,f1120])).

fof(f1120,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1116,f1090])).

fof(f1090,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f531,f1086])).

fof(f1116,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f1089,f68])).

fof(f1089,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f530,f1086])).

fof(f1092,plain,(
    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f535,f1086])).

fof(f1135,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1134,f1022])).

fof(f1022,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f32,f1021])).

fof(f1134,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1128,f1023])).

fof(f1023,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f106,f1021])).

fof(f1128,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f1107])).

fof(f1107,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1098,f1106])).

fof(f1106,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1101,f1095])).

fof(f1095,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1026,f1086])).

fof(f1026,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f526,f1021])).

fof(f1101,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f1094,f68])).

fof(f1094,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1025,f1086])).

fof(f1025,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f525,f1021])).

fof(f1098,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1029,f1086])).

fof(f1029,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f533,f1021])).

fof(f1272,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1264,f58])).

fof(f1264,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1263,f1187])).

fof(f1187,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1186,f88])).

fof(f1186,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1185,f115])).

fof(f1185,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1184,f67])).

fof(f1184,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f1137,f1121])).

fof(f1137,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f1136,f1023])).

fof(f1136,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f1129,f1022])).

fof(f1129,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f48,f1107])).

fof(f1263,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1262,f1023])).

fof(f1262,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1256,f1022])).

fof(f1256,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1181,f1179])).

fof(f1181,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f1158,f1163])).

fof(f1163,plain,
    ( r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1162,f88])).

fof(f1162,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1161,f115])).

fof(f1161,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1160,f67])).

fof(f1160,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f1133,f1121])).

fof(f1133,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f1132,f1023])).

fof(f1132,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f1127,f1022])).

fof(f1127,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f47,f1107])).

fof(f1158,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(subsumption_resolution,[],[f1157,f115])).

fof(f1157,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(subsumption_resolution,[],[f1148,f88])).

fof(f1148,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(superposition,[],[f49,f1121])).

fof(f1325,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) != k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f1192,f1296])).

fof(f1296,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1294,f1178])).

fof(f1178,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1168,f1099])).

fof(f1099,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f1088,f51])).

fof(f1088,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ m1_subset_1(X1,k1_xboole_0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1 ) ),
    inference(backward_demodulation,[],[f529,f1086])).

fof(f1294,plain,
    ( sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1261,f58])).

fof(f1261,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1260,f1187])).

fof(f1260,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1259,f1023])).

fof(f1259,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1255,f1022])).

fof(f1255,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1181,f1178])).

fof(f1192,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1191,f115])).

fof(f1191,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1190,f88])).

fof(f1190,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1189,f67])).

fof(f1189,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f1139,f1121])).

fof(f1139,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1138,f1022])).

fof(f1138,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1130,f1023])).

fof(f1130,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f48,f1107])).

fof(f1333,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f1331])).

fof(f1331,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1324,f58])).

fof(f1324,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1323,f1247])).

fof(f1247,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1245,f1170])).

fof(f1170,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1163,f1100])).

fof(f1245,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1244,f58])).

fof(f1244,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1243,f1192])).

fof(f1243,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1242,f88])).

fof(f1242,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1236,f115])).

fof(f1236,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1177,f1170])).

fof(f1177,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
      | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ) ),
    inference(resolution,[],[f1168,f1141])).

fof(f1141,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f1140,f1023])).

fof(f1140,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f1131,f1022])).

fof(f1131,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f49,f1107])).

fof(f1323,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f1187,f1285])).

fof(f1285,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1283,f1169])).

fof(f1169,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1163,f1099])).

fof(f1283,plain,
    ( sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1241,f58])).

fof(f1241,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1240,f1192])).

fof(f1240,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1239,f88])).

fof(f1239,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1235,f115])).

fof(f1235,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1177,f1169])).

fof(f1096,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1027,f1086])).

fof(f1027,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f527,f1021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (6993)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (6999)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (6994)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (6991)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (7010)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (6988)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (6992)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (6994)Refutation not found, incomplete strategy% (6994)------------------------------
% 0.22/0.51  % (6994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7008)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (7011)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (6999)Refutation not found, incomplete strategy% (6999)------------------------------
% 0.22/0.51  % (6999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7002)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (7003)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (6997)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (7012)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (7005)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (7001)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (6995)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (6996)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (6988)Refutation not found, incomplete strategy% (6988)------------------------------
% 0.22/0.52  % (6988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6988)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6988)Memory used [KB]: 10618
% 0.22/0.52  % (6988)Time elapsed: 0.105 s
% 0.22/0.52  % (6988)------------------------------
% 0.22/0.52  % (6988)------------------------------
% 0.22/0.52  % (6995)Refutation not found, incomplete strategy% (6995)------------------------------
% 0.22/0.52  % (6995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6995)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6995)Memory used [KB]: 1663
% 0.22/0.52  % (6995)Time elapsed: 0.070 s
% 0.22/0.52  % (6995)------------------------------
% 0.22/0.52  % (6995)------------------------------
% 0.22/0.53  % (7001)Refutation not found, incomplete strategy% (7001)------------------------------
% 0.22/0.53  % (7001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7001)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7001)Memory used [KB]: 6268
% 0.22/0.53  % (7001)Time elapsed: 0.120 s
% 0.22/0.53  % (7001)------------------------------
% 0.22/0.53  % (7001)------------------------------
% 0.22/0.53  % (6994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6994)Memory used [KB]: 10746
% 0.22/0.53  % (6994)Time elapsed: 0.097 s
% 0.22/0.53  % (6994)------------------------------
% 0.22/0.53  % (6994)------------------------------
% 0.22/0.53  % (6999)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6999)Memory used [KB]: 10746
% 0.22/0.53  % (6999)Time elapsed: 0.099 s
% 0.22/0.53  % (6999)------------------------------
% 0.22/0.53  % (6999)------------------------------
% 0.22/0.54  % (7013)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (7000)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (6989)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (6990)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (6993)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (6998)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (7004)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (7009)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (7007)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f1369,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f1342,f1097])).
% 0.22/0.55  fof(f1097,plain,(
% 0.22/0.55    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f1028,f1086])).
% 0.22/0.55  fof(f1086,plain,(
% 0.22/0.55    k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1030,f1028])).
% 0.22/0.55  fof(f1030,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.55    inference(backward_demodulation,[],[f572,f1021])).
% 0.22/0.55  fof(f1021,plain,(
% 0.22/0.55    k1_xboole_0 = sK2),
% 0.22/0.55    inference(subsumption_resolution,[],[f943,f532])).
% 0.22/0.55  fof(f532,plain,(
% 0.22/0.55    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2)),
% 0.22/0.55    inference(backward_demodulation,[],[f99,f523])).
% 0.22/0.55  fof(f523,plain,(
% 0.22/0.55    k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f446,f99])).
% 0.22/0.55  fof(f446,plain,(
% 0.22/0.55    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.55    inference(superposition,[],[f35,f435])).
% 0.22/0.55  fof(f435,plain,(
% 0.22/0.55    sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f429,f434])).
% 0.22/0.55  fof(f434,plain,(
% 0.22/0.55    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f433,f269])).
% 0.22/0.55  fof(f269,plain,(
% 0.22/0.55    k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f268,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f12])).
% 0.22/0.55  fof(f12,conjecture,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f260,f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f104,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f34,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.55    inference(resolution,[],[f185,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f184,f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    v1_relat_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f114,f53])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.55    inference(resolution,[],[f94,f52])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f93,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ~v2_struct_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f92,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    l1_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.55    inference(subsumption_resolution,[],[f78,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    v2_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.55    inference(resolution,[],[f37,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    m1_pre_topc(sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f174,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f87,f38])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f86,f40])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f76,f39])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f37,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK3(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(superposition,[],[f48,f168])).
% 0.22/0.56  fof(f168,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f165])).
% 0.22/0.56  fof(f165,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(superposition,[],[f127,f134])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f131])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(superposition,[],[f109,f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    u1_struct_0(sK1) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f97,f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f34,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f95,f34])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.56    inference(resolution,[],[f33,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f107,f94])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.56    inference(resolution,[],[f91,f64])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f90,f38])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f89,f40])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f77,f39])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f37,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(superposition,[],[f113,f105])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f94,f55])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).
% 0.22/0.56  fof(f433,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f432,f88])).
% 0.22/0.56  fof(f432,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f431,f115])).
% 0.22/0.56  fof(f431,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f425])).
% 0.22/0.56  fof(f425,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(resolution,[],[f424,f241])).
% 0.22/0.56  fof(f241,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f240,f106])).
% 0.22/0.56  fof(f240,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f238,f32])).
% 0.22/0.56  fof(f238,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0)) )),
% 0.22/0.56    inference(resolution,[],[f237,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f237,plain,(
% 0.22/0.56    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f236,f32])).
% 0.22/0.56  fof(f236,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f230,f106])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f181,f67])).
% 0.22/0.56  fof(f181,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f180,f115])).
% 0.22/0.56  fof(f180,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f172,f88])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(superposition,[],[f47,f168])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f424,plain,(
% 0.22/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f423,f276])).
% 0.22/0.56  fof(f276,plain,(
% 0.22/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f275,f217])).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f216,f106])).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f210,f32])).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f179,f67])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f178,f88])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f171,f115])).
% 0.22/0.56  fof(f171,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(superposition,[],[f47,f168])).
% 0.22/0.56  fof(f275,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f274])).
% 0.22/0.56  fof(f274,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(superposition,[],[f271,f105])).
% 0.22/0.56  fof(f271,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f247,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f247,plain,(
% 0.22/0.56    m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f246])).
% 0.22/0.56  fof(f246,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f227,f121])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_relat_1(sK2)) | m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(superposition,[],[f81,f105])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f80,f38])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f79,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ~v2_struct_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f74,f40])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.56    inference(resolution,[],[f37,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f217,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.56  fof(f423,plain,(
% 0.22/0.56    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f422])).
% 0.22/0.56  fof(f422,plain,(
% 0.22/0.56    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(superposition,[],[f257,f364])).
% 0.22/0.56  fof(f364,plain,(
% 0.22/0.56    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f357,f363])).
% 0.22/0.56  fof(f363,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f362,f269])).
% 0.22/0.56  fof(f362,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f361,f88])).
% 0.22/0.56  fof(f361,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f360,f115])).
% 0.22/0.56  fof(f360,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f355])).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(resolution,[],[f341,f241])).
% 0.22/0.56  fof(f341,plain,(
% 0.22/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f340,f217])).
% 0.22/0.56  fof(f340,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f339])).
% 0.22/0.56  fof(f339,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(superposition,[],[f270,f105])).
% 0.22/0.56  fof(f270,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f247,f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f84,f38])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f83,f36])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f82,f40])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f75,f39])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(resolution,[],[f37,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f341,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f257,plain,(
% 0.22/0.56    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f256,f106])).
% 0.22/0.56  fof(f256,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f248,f32])).
% 0.22/0.56  fof(f248,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f183,f67])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f182,f88])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X2) | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f173,f115])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X2) | k1_funct_1(X2,sK3(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.22/0.56    inference(superposition,[],[f48,f168])).
% 0.22/0.56  fof(f429,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f427])).
% 0.22/0.56  fof(f427,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f424,f58])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f98,f34])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f96,f32])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 0.22/0.56    inference(resolution,[],[f33,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.22/0.56    inference(equality_resolution,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.22/0.56  fof(f943,plain,(
% 0.22/0.56    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f527,f910])).
% 0.22/0.56  fof(f910,plain,(
% 0.22/0.56    sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f907,f900])).
% 0.22/0.56  fof(f900,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f898,f741])).
% 0.22/0.56  fof(f741,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f740,f669])).
% 0.22/0.56  fof(f669,plain,(
% 0.22/0.56    r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f668,f115])).
% 0.22/0.56  fof(f668,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f667,f88])).
% 0.22/0.56  fof(f667,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f665,f67])).
% 0.22/0.56  fof(f665,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f664])).
% 0.22/0.56  fof(f664,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f608,f639])).
% 0.22/0.56  fof(f639,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f636])).
% 0.22/0.56  fof(f636,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f576,f589])).
% 0.22/0.56  fof(f589,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f584,f558])).
% 0.22/0.56  fof(f558,plain,(
% 0.22/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f531,f540])).
% 0.22/0.56  fof(f540,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f537,f526])).
% 0.22/0.56  fof(f526,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f34,f523])).
% 0.22/0.56  fof(f537,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 0.22/0.56    inference(resolution,[],[f525,f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.22/0.56    inference(equality_resolution,[],[f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f525,plain,(
% 0.22/0.56    v1_funct_2(sK2,u1_struct_0(sK1),k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f33,f523])).
% 0.22/0.56  fof(f531,plain,(
% 0.22/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f94,f523])).
% 0.22/0.56  fof(f584,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(resolution,[],[f557,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.56    inference(equality_resolution,[],[f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f557,plain,(
% 0.22/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f530,f540])).
% 0.22/0.56  fof(f530,plain,(
% 0.22/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f91,f523])).
% 0.22/0.56  fof(f576,plain,(
% 0.22/0.56    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f535,f540])).
% 0.22/0.56  fof(f535,plain,(
% 0.22/0.56    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f113,f523])).
% 0.22/0.56  fof(f608,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f607,f32])).
% 0.22/0.56  fof(f607,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f601,f106])).
% 0.22/0.56  fof(f601,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(superposition,[],[f47,f599])).
% 0.22/0.56  fof(f599,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f596])).
% 0.22/0.56  fof(f596,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f569,f565])).
% 0.22/0.56  fof(f565,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f560,f554])).
% 0.22/0.56  fof(f554,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f526,f540])).
% 0.22/0.56  fof(f560,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(resolution,[],[f553,f68])).
% 0.22/0.56  fof(f553,plain,(
% 0.22/0.56    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f525,f540])).
% 0.22/0.56  fof(f569,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f533,f540])).
% 0.22/0.56  fof(f533,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f103,f523])).
% 0.22/0.56  fof(f740,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f739])).
% 0.22/0.56  fof(f739,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f690,f540])).
% 0.22/0.56  fof(f690,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.22/0.56    inference(resolution,[],[f675,f524])).
% 0.22/0.56  fof(f524,plain,(
% 0.22/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_xboole_0) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 0.22/0.56    inference(backward_demodulation,[],[f31,f523])).
% 0.22/0.56  fof(f675,plain,(
% 0.22/0.56    m1_subset_1(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | k1_xboole_0 = sK2 | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(resolution,[],[f669,f51])).
% 0.22/0.56  fof(f898,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f897])).
% 0.22/0.56  fof(f897,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(superposition,[],[f711,f816])).
% 0.22/0.56  fof(f816,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f808,f815])).
% 0.22/0.56  fof(f815,plain,(
% 0.22/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f814,f703])).
% 0.22/0.56  fof(f703,plain,(
% 0.22/0.56    k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f702,f88])).
% 0.22/0.56  fof(f702,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f701,f115])).
% 0.22/0.56  fof(f701,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f698,f67])).
% 0.22/0.56  fof(f698,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f697])).
% 0.22/0.56  fof(f697,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f610,f639])).
% 0.22/0.56  fof(f610,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f609,f106])).
% 0.22/0.56  fof(f609,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f602,f32])).
% 0.22/0.56  fof(f602,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK3(sK2,X2)) != k1_funct_1(X2,sK3(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(superposition,[],[f48,f599])).
% 0.22/0.56  fof(f814,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f813,f106])).
% 0.22/0.56  fof(f813,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(sK2) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f812,f32])).
% 0.22/0.56  fof(f812,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(sK2) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f806])).
% 0.22/0.56  fof(f806,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f764,f695])).
% 0.22/0.56  fof(f695,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(X0) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1))) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f692])).
% 0.22/0.56  fof(f692,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k4_tmap_1(sK0,sK1),X0) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(resolution,[],[f655,f662])).
% 0.22/0.56  fof(f662,plain,(
% 0.22/0.56    r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f661,f88])).
% 0.22/0.56  fof(f661,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f660,f115])).
% 0.22/0.56  fof(f660,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f658,f67])).
% 0.22/0.56  fof(f658,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f657])).
% 0.22/0.56  fof(f657,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f606,f639])).
% 0.22/0.56  fof(f606,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f605,f106])).
% 0.22/0.56  fof(f605,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f600,f32])).
% 0.22/0.56  fof(f600,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | r2_hidden(sK3(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(superposition,[],[f47,f599])).
% 0.22/0.56  fof(f655,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f654,f115])).
% 0.22/0.56  fof(f654,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f645,f88])).
% 0.22/0.56  fof(f645,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(superposition,[],[f49,f639])).
% 0.22/0.56  fof(f764,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f763,f669])).
% 0.22/0.56  fof(f763,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f762])).
% 0.22/0.56  fof(f762,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f689,f540])).
% 0.22/0.56  fof(f689,plain,(
% 0.22/0.56    ~r2_hidden(sK3(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2))),
% 0.22/0.56    inference(resolution,[],[f675,f529])).
% 0.22/0.56  fof(f529,plain,(
% 0.22/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_xboole_0) | ~r2_hidden(X1,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(backward_demodulation,[],[f85,f523])).
% 0.22/0.56  fof(f808,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f764,f58])).
% 0.22/0.56  fof(f711,plain,(
% 0.22/0.56    k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f710,f115])).
% 0.22/0.56  fof(f710,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f709,f88])).
% 0.22/0.56  fof(f709,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f706,f67])).
% 0.22/0.56  fof(f706,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f705])).
% 0.22/0.56  fof(f705,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f612,f639])).
% 0.22/0.56  fof(f612,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f611,f32])).
% 0.22/0.56  fof(f611,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_funct_1(sK2) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f603,f106])).
% 0.22/0.56  fof(f603,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,sK2)) != k1_funct_1(sK2,sK3(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(superposition,[],[f48,f599])).
% 0.22/0.56  fof(f907,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f903])).
% 0.22/0.56  fof(f903,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f884,f58])).
% 0.22/0.56  fof(f884,plain,(
% 0.22/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f882,f734])).
% 0.22/0.56  fof(f734,plain,(
% 0.22/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f733,f662])).
% 0.22/0.56  fof(f733,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f732])).
% 0.22/0.56  fof(f732,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f683,f540])).
% 0.22/0.56  fof(f683,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f670,f524])).
% 0.22/0.56  fof(f670,plain,(
% 0.22/0.56    m1_subset_1(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f662,f51])).
% 0.22/0.56  fof(f882,plain,(
% 0.22/0.56    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f881])).
% 0.22/0.56  fof(f881,plain,(
% 0.22/0.56    sK3(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK3(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(superposition,[],[f703,f790])).
% 0.22/0.56  fof(f790,plain,(
% 0.22/0.56    sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f782,f789])).
% 0.22/0.56  fof(f789,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f788,f711])).
% 0.22/0.56  fof(f788,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f787,f88])).
% 0.22/0.56  fof(f787,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f786,f115])).
% 0.22/0.56  fof(f786,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f780])).
% 0.22/0.56  fof(f780,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2 | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(resolution,[],[f745,f677])).
% 0.22/0.56  fof(f677,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | k1_xboole_0 = sK2 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f674])).
% 0.22/0.56  fof(f674,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK3(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(resolution,[],[f669,f614])).
% 0.22/0.56  fof(f614,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f613,f106])).
% 0.22/0.56  fof(f613,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(sK2) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f604,f32])).
% 0.22/0.56  fof(f604,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(sK2) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 0.22/0.56    inference(superposition,[],[f49,f599])).
% 0.22/0.56  fof(f745,plain,(
% 0.22/0.56    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f744,f662])).
% 0.22/0.56  fof(f744,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f743])).
% 0.22/0.56  fof(f743,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f682,f540])).
% 0.22/0.56  fof(f682,plain,(
% 0.22/0.56    ~r2_hidden(sK3(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f670,f529])).
% 0.22/0.56  fof(f782,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | sK3(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f745,f58])).
% 0.22/0.56  fof(f527,plain,(
% 0.22/0.56    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f35,f523])).
% 0.22/0.56  fof(f572,plain,(
% 0.22/0.56    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.56    inference(superposition,[],[f527,f549])).
% 0.22/0.56  fof(f549,plain,(
% 0.22/0.56    k1_xboole_0 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f546,f531])).
% 0.22/0.56  fof(f546,plain,(
% 0.22/0.56    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 0.22/0.56    inference(resolution,[],[f530,f70])).
% 0.22/0.56  fof(f1028,plain,(
% 0.22/0.56    r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f532,f1021])).
% 0.22/0.56  fof(f1342,plain,(
% 0.22/0.56    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f1096,f1336])).
% 0.22/0.56  fof(f1336,plain,(
% 0.22/0.56    k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1333,f1326])).
% 0.22/0.56  fof(f1326,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1325,f1274])).
% 0.22/0.56  fof(f1274,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1272,f1179])).
% 0.22/0.56  fof(f1179,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(resolution,[],[f1168,f1100])).
% 0.22/0.56  fof(f1100,plain,(
% 0.22/0.56    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | k1_funct_1(k1_xboole_0,X3) = X3) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1093,f51])).
% 0.22/0.56  fof(f1093,plain,(
% 0.22/0.56    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | k1_funct_1(k1_xboole_0,X3) = X3 | ~m1_subset_1(X3,k1_xboole_0)) )),
% 0.22/0.56    inference(backward_demodulation,[],[f1024,f1086])).
% 0.22/0.56  fof(f1024,plain,(
% 0.22/0.56    ( ! [X3] : (k1_funct_1(k1_xboole_0,X3) = X3 | ~m1_subset_1(X3,k1_xboole_0) | ~r2_hidden(X3,u1_struct_0(sK1))) )),
% 0.22/0.56    inference(backward_demodulation,[],[f524,f1021])).
% 0.22/0.56  fof(f1168,plain,(
% 0.22/0.56    r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1167,f115])).
% 0.22/0.56  fof(f1167,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1166,f88])).
% 0.22/0.56  fof(f1166,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1165,f67])).
% 0.22/0.56  fof(f1165,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(superposition,[],[f1135,f1121])).
% 0.22/0.56  fof(f1121,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f1092,f1120])).
% 0.22/0.56  fof(f1120,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1116,f1090])).
% 0.22/0.56  fof(f1090,plain,(
% 0.22/0.56    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f531,f1086])).
% 0.22/0.56  fof(f1116,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(resolution,[],[f1089,f68])).
% 0.22/0.56  fof(f1089,plain,(
% 0.22/0.56    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f530,f1086])).
% 0.22/0.56  fof(f1092,plain,(
% 0.22/0.56    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f535,f1086])).
% 0.22/0.56  fof(f1135,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1134,f1022])).
% 0.22/0.56  fof(f1022,plain,(
% 0.22/0.56    v1_funct_1(k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f32,f1021])).
% 0.22/0.56  fof(f1134,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1128,f1023])).
% 0.22/0.56  fof(f1023,plain,(
% 0.22/0.56    v1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f106,f1021])).
% 0.22/0.56  fof(f1128,plain,(
% 0.22/0.56    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X1) | r2_hidden(sK3(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f47,f1107])).
% 0.22/0.56  fof(f1107,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f1098,f1106])).
% 0.22/0.56  fof(f1106,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1101,f1095])).
% 0.22/0.56  fof(f1095,plain,(
% 0.22/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f1026,f1086])).
% 0.22/0.56  fof(f1026,plain,(
% 0.22/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f526,f1021])).
% 0.22/0.56  fof(f1101,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.56    inference(resolution,[],[f1094,f68])).
% 0.22/0.56  fof(f1094,plain,(
% 0.22/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f1025,f1086])).
% 0.22/0.56  fof(f1025,plain,(
% 0.22/0.56    v1_funct_2(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f525,f1021])).
% 0.22/0.56  fof(f1098,plain,(
% 0.22/0.56    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f1029,f1086])).
% 0.22/0.56  fof(f1029,plain,(
% 0.22/0.56    k1_relat_1(k1_xboole_0) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f533,f1021])).
% 0.22/0.56  fof(f1272,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f1264,f58])).
% 0.22/0.56  fof(f1264,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1263,f1187])).
% 0.22/0.56  fof(f1187,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1186,f88])).
% 0.22/0.56  fof(f1186,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1185,f115])).
% 0.22/0.56  fof(f1185,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1184,f67])).
% 0.22/0.56  fof(f1184,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(superposition,[],[f1137,f1121])).
% 0.22/0.56  fof(f1137,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1136,f1023])).
% 0.22/0.56  fof(f1136,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1129,f1022])).
% 0.22/0.56  fof(f1129,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X2)) != k1_funct_1(X2,sK3(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 0.22/0.56    inference(superposition,[],[f48,f1107])).
% 0.22/0.56  fof(f1263,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1262,f1023])).
% 0.22/0.56  fof(f1262,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1256,f1022])).
% 0.22/0.56  fof(f1256,plain,(
% 0.22/0.56    ~v1_funct_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(resolution,[],[f1181,f1179])).
% 0.22/0.56  fof(f1181,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(X0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))) )),
% 0.22/0.56    inference(resolution,[],[f1158,f1163])).
% 0.22/0.56  fof(f1163,plain,(
% 0.22/0.56    r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1162,f88])).
% 0.22/0.56  fof(f1162,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1161,f115])).
% 0.22/0.56  fof(f1161,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1160,f67])).
% 0.22/0.56  fof(f1160,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 0.22/0.56    inference(superposition,[],[f1133,f1121])).
% 0.22/0.56  fof(f1133,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1132,f1023])).
% 0.22/0.56  fof(f1132,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1127,f1022])).
% 0.22/0.56  fof(f1127,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(superposition,[],[f47,f1107])).
% 0.22/0.56  fof(f1158,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1157,f115])).
% 0.22/0.56  fof(f1157,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1148,f88])).
% 0.22/0.56  fof(f1148,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 0.22/0.56    inference(superposition,[],[f49,f1121])).
% 0.22/0.56  fof(f1325,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) != k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(superposition,[],[f1192,f1296])).
% 0.22/0.56  fof(f1296,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1294,f1178])).
% 0.22/0.56  fof(f1178,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(resolution,[],[f1168,f1099])).
% 0.22/0.56  fof(f1099,plain,(
% 0.22/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1088,f51])).
% 0.22/0.56  fof(f1088,plain,(
% 0.22/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~m1_subset_1(X1,k1_xboole_0) | k1_funct_1(k4_tmap_1(sK0,sK1),X1) = X1) )),
% 0.22/0.56    inference(backward_demodulation,[],[f529,f1086])).
% 0.22/0.56  fof(f1294,plain,(
% 0.22/0.56    sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f1261,f58])).
% 0.22/0.56  fof(f1261,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1260,f1187])).
% 0.22/0.56  fof(f1260,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1259,f1023])).
% 0.22/0.56  fof(f1259,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1255,f1022])).
% 0.22/0.56  fof(f1255,plain,(
% 0.22/0.56    ~v1_funct_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 0.22/0.56    inference(resolution,[],[f1181,f1178])).
% 0.22/0.56  fof(f1192,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1191,f115])).
% 0.22/0.56  fof(f1191,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1190,f88])).
% 0.22/0.56  fof(f1190,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1189,f67])).
% 0.22/0.56  fof(f1189,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(superposition,[],[f1139,f1121])).
% 0.22/0.56  fof(f1139,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1138,f1022])).
% 0.22/0.56  fof(f1138,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1130,f1023])).
% 0.22/0.56  fof(f1130,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X3) | k1_funct_1(X3,sK3(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f48,f1107])).
% 0.22/0.56  fof(f1333,plain,(
% 0.22/0.56    k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f1331])).
% 0.22/0.56  fof(f1331,plain,(
% 0.22/0.56    k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f1324,f58])).
% 0.22/0.56  fof(f1324,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1323,f1247])).
% 0.22/0.56  fof(f1247,plain,(
% 0.22/0.56    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1245,f1170])).
% 0.22/0.56  fof(f1170,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f1163,f1100])).
% 0.22/0.56  fof(f1245,plain,(
% 0.22/0.56    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f1244,f58])).
% 0.22/0.56  fof(f1244,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1243,f1192])).
% 0.22/0.56  fof(f1243,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1242,f88])).
% 0.22/0.56  fof(f1242,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1236,f115])).
% 0.22/0.56  fof(f1236,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f1177,f1170])).
% 0.22/0.56  fof(f1177,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(X0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)) )),
% 0.22/0.56    inference(resolution,[],[f1168,f1141])).
% 0.22/0.56  fof(f1141,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1140,f1023])).
% 0.22/0.56  fof(f1140,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f1131,f1022])).
% 0.22/0.56  fof(f1131,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 0.22/0.56    inference(superposition,[],[f49,f1107])).
% 0.22/0.56  fof(f1323,plain,(
% 0.22/0.56    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(superposition,[],[f1187,f1285])).
% 0.22/0.56  fof(f1285,plain,(
% 0.22/0.56    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1283,f1169])).
% 0.22/0.56  fof(f1169,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f1163,f1099])).
% 0.22/0.56  fof(f1283,plain,(
% 0.22/0.56    sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f1241,f58])).
% 0.22/0.56  fof(f1241,plain,(
% 0.22/0.56    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1240,f1192])).
% 0.22/0.56  fof(f1240,plain,(
% 0.22/0.56    k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1239,f88])).
% 0.22/0.56  fof(f1239,plain,(
% 0.22/0.56    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f1235,f115])).
% 0.22/0.56  fof(f1235,plain,(
% 0.22/0.56    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f1177,f1169])).
% 0.22/0.56  fof(f1096,plain,(
% 0.22/0.56    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f1027,f1086])).
% 0.22/0.56  fof(f1027,plain,(
% 0.22/0.56    ~r2_funct_2(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 0.22/0.56    inference(backward_demodulation,[],[f527,f1021])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (6993)------------------------------
% 0.22/0.56  % (6993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6993)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (6993)Memory used [KB]: 6524
% 0.22/0.56  % (6993)Time elapsed: 0.119 s
% 0.22/0.56  % (6993)------------------------------
% 0.22/0.56  % (6993)------------------------------
% 0.22/0.56  % (6987)Success in time 0.198 s
%------------------------------------------------------------------------------
